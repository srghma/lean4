// Lean compiler output
// Module: Lake.Toml.ParserUtil
// Imports: Lean.PrettyPrinter.Formatter Lean.PrettyPrinter.Parenthesizer Lean.Parser
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instBEq_beq___redArg;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_trimAscii;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_mkLit;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Syntax_getKind};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_ParserContext_mkEmptySubstringAt, l_Lean_Parser_andthen, l_Lean_Parser_atomicFn,
    l_Lean_Parser_checkLinebreakBefore, l_Lean_Parser_epsilonInfo, l_Lean_Parser_mkAntiquot,
    l_Lean_Parser_pushNone, l_Lean_Parser_sepBy1NoAntiquot, l_Lean_Parser_sepByNoAntiquot,
    l_Lean_Parser_symbol, l_Lean_Parser_takeWhileFn, l_Lean_Parser_withAntiquot,
    l_Lean_Parser_withAntiquotSpliceAndSuffix,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_mkAntiquot_formatter___boxed, l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_symbol_formatter___boxed, l_Lean_Parser_symbol_parenthesizer___boxed,
    l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed,
    l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Types::{
    l_Lean_Parser_InputContext_atEnd, l_Lean_Parser_ParserState_mkEOIError,
    l_Lean_Parser_ParserState_mkUnexpectedError, l_Lean_Parser_ParserState_next_x27___redArg,
    l_Lean_Parser_ParserState_popSyntax, l_Lean_Parser_ParserState_pushSyntax,
    l_Lean_Parser_ParserState_restore, l_Lean_Parser_ParserState_stackSize,
    l_Lean_Parser_SyntaxStack_back, l_Lean_Parser_instBEqError_beq,
    l_Lean_Parser_instBEqError_beq___boxed, l_Lean_Parser_withCache,
};
use crate::r#gen::Lean::Parser::{initialize_Lean_Parser, runtime_initialize_Lean_Parser};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    initialize_Lean_PrettyPrinter_Formatter,
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe,
    l_Lean_PrettyPrinter_Formatter_getExprPos_x3f, l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_pushToken___boxed,
    l_Lean_PrettyPrinter_Formatter_rawCh_formatter,
    l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter,
    l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg,
    l_Lean_PrettyPrinter_Formatter_visitAtom, l_Lean_PrettyPrinter_Formatter_withMaybeTag,
    l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed,
    runtime_initialize_Lean_PrettyPrinter_Formatter,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    initialize_Lean_PrettyPrinter_Parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe,
    l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed,
    runtime_initialize_Lean_PrettyPrinter_Parenthesizer,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_Traverser_left;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_push;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0_value:
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
    m_fun: l_Lean_Parser_instBEqError_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_instAndThenParserFn__lake___closed__0_value:
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
    m_fun: l_Lake_Toml_instAndThenParserFn__lake___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_instAndThenParserFn__lake___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instAndThenParserFn__lake___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_Toml_instAndThenParserFn__lake: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instAndThenParserFn__lake___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_mkUnexpectedCharError___closed__0_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lake_Toml_mkUnexpectedCharError___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mkUnexpectedCharError___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_mkUnexpectedCharError___closed__1_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Toml_mkUnexpectedCharError___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mkUnexpectedCharError___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_mkUnexpectedCharError___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Lake_Toml_mkUnexpectedCharError___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_mkUnexpectedCharError___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByChar1Fn___closed__0_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
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
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 101, 112, 97, 114, 97, 116,
            111, 114, 32, 39, 0,
        ],
    };
static mut l_Lake_Toml_sepByChar1Fn___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByChar1Fn___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_atom___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_atom___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_Toml_atom___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_atom___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_atom___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_atom___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_atom___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom_formatter___redArg___closed__0_value: crate::leanh::LeanStringObject<
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
        80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0,
    ],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom_formatter___redArg___closed__1_value: crate::leanh::LeanStringObject<
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
    m_data: [102, 111, 114, 109, 97, 116, 0],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom_formatter___redArg___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [98, 97, 99, 107, 116, 114, 97, 99, 107, 0],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        61860673417901001 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6523374221730715651 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_Toml_atom_formatter___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            3944321918363561809 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_atom_formatter___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom_formatter___redArg___closed__4_value: crate::leanh::LeanStringObject<
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
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_atom_formatter___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Toml_atom_formatter___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_atom_formatter___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_atom_formatter___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_atom_formatter___redArg___closed__7_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 39, 0,
    ],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_atom_formatter___redArg___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_atom_formatter___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_atom_formatter___redArg___closed__9_value: crate::leanh::LeanStringObject<
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
        39, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 111, 109, 0,
    ],
};
static mut l_Lake_Toml_atom_formatter___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_atom_formatter___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_atom_formatter___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_atom_formatter___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0_value:
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
    m_fun: l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Formatter_visitArgs_spec__1___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value:
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
    m_data: [115, 101, 112, 66, 121, 0],
};
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10608024464111057092 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value:
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
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Syntax_MonadTraverser_goLeft___at___00Lean_PrettyPrinter_Parenthesizer_visitArgs_spec__1___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_Toml_sepByLinebreak___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_sepByLinebreak___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Toml_sepByLinebreak___closed__1_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0],
    };
static mut l_Lake_Toml_sepByLinebreak___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_sepByLinebreak___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_Toml_sepByLinebreak___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_sepByLinebreak___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_Toml_sepByLinebreak___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_sepByLinebreak___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lake_Toml_isBinDigit(mut v_c_1693_: u32) -> u8 {
    let mut v___x_1694_: u32 = 0;
    let mut v___x_1695_: u8 = 0;
    v___x_1694_ = 48;
    v___x_1695_ = lean_uint32_dec_eq(v_c_1693_, v___x_1694_);
    if v___x_1695_ == 0 {
        let mut v___x_1696_: u32 = 0;
        let mut v___x_1697_: u8 = 0;
        v___x_1696_ = 49;
        v___x_1697_ = lean_uint32_dec_eq(v_c_1693_, v___x_1696_);
        return v___x_1697_;
    } else {
        return v___x_1695_;
    }
}
pub unsafe fn l_Lake_Toml_isBinDigit___boxed(
    mut v_c_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1699_: u32 = 0;
    let mut v_res_1700_: u8 = 0;
    let mut v_r_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1699_ = crate::leanh::lean_unbox_uint32(v_c_1698_);
    crate::leanh::lean_dec(v_c_1698_);
    v_res_1700_ = l_Lake_Toml_isBinDigit(v_c_boxed_1699_);
    v_r_1701_ = crate::leanh::lean_box((v_res_1700_) as usize);
    return v_r_1701_;
}
pub unsafe fn l_Lake_Toml_isOctDigit(mut v_c_1702_: u32) -> u8 {
    let mut v___x_1703_: u32 = 0;
    let mut v___x_1704_: u8 = 0;
    v___x_1703_ = 48;
    v___x_1704_ = lean_uint32_dec_le(v___x_1703_, v_c_1702_);
    if v___x_1704_ == 0 {
        return v___x_1704_;
    } else {
        let mut v___x_1705_: u32 = 0;
        let mut v___x_1706_: u8 = 0;
        v___x_1705_ = 55;
        v___x_1706_ = lean_uint32_dec_le(v_c_1702_, v___x_1705_);
        return v___x_1706_;
    }
}
pub unsafe fn l_Lake_Toml_isOctDigit___boxed(
    mut v_c_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1708_: u32 = 0;
    let mut v_res_1709_: u8 = 0;
    let mut v_r_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1708_ = crate::leanh::lean_unbox_uint32(v_c_1707_);
    crate::leanh::lean_dec(v_c_1707_);
    v_res_1709_ = l_Lake_Toml_isOctDigit(v_c_boxed_1708_);
    v_r_1710_ = crate::leanh::lean_box((v_res_1709_) as usize);
    return v_r_1710_;
}
pub unsafe fn l_Lake_Toml_isHexDigit(mut v_c_1711_: u32) -> u8 {
    let mut v___y_1713_: u8 = 0;
    let mut v___x_1714_: u32 = 0;
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: u32 = 0;
    let mut v___x_1717_: u8 = 0;
    let mut v___y_1719_: u8 = 0;
    let mut v___x_1720_: u32 = 0;
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: u32 = 0;
    let mut v___x_1723_: u8 = 0;
    let mut v___x_1724_: u32 = 0;
    let mut v___x_1725_: u8 = 0;
    let mut v___x_1726_: u32 = 0;
    let mut v___x_1727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1724_ = 48;
                v___x_1725_ = lean_uint32_dec_le(v___x_1724_, v_c_1711_);
                if v___x_1725_ == 0 {
                    v___y_1719_ = v___x_1725_;
                    state = 2;
                    continue;
                } else {
                    v___x_1726_ = 57;
                    v___x_1727_ = lean_uint32_dec_le(v_c_1711_, v___x_1726_);
                    v___y_1719_ = v___x_1727_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1713_ == 0 {
                    v___x_1714_ = 65;
                    v___x_1715_ = lean_uint32_dec_le(v___x_1714_, v_c_1711_);
                    if v___x_1715_ == 0 {
                        return v___x_1715_;
                    } else {
                        v___x_1716_ = 70;
                        v___x_1717_ = lean_uint32_dec_le(v_c_1711_, v___x_1716_);
                        return v___x_1717_;
                    }
                } else {
                    return v___y_1713_;
                }
            }
            2 => {
                if v___y_1719_ == 0 {
                    v___x_1720_ = 97;
                    v___x_1721_ = lean_uint32_dec_le(v___x_1720_, v_c_1711_);
                    if v___x_1721_ == 0 {
                        v___y_1713_ = v___x_1721_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1722_ = 102;
                        v___x_1723_ = lean_uint32_dec_le(v_c_1711_, v___x_1722_);
                        v___y_1713_ = v___x_1723_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1719_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_isHexDigit___boxed(
    mut v_c_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1729_: u32 = 0;
    let mut v_res_1730_: u8 = 0;
    let mut v_r_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1729_ = crate::leanh::lean_unbox_uint32(v_c_1728_);
    crate::leanh::lean_dec(v_c_1728_);
    v_res_1730_ = l_Lake_Toml_isHexDigit(v_c_boxed_1729_);
    v_r_1731_ = crate::leanh::lean_box((v_res_1730_) as usize);
    return v_r_1731_;
}
pub unsafe fn l_Lake_Toml_skipFn___redArg(
    mut v_s_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1732_);
    return v_s_1732_;
}
pub unsafe fn l_Lake_Toml_skipFn___redArg___boxed(
    mut v_s_1733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Lake_Toml_skipFn___redArg(v_s_1733_);
    crate::leanh::lean_dec_ref(v_s_1733_);
    return v_res_1734_;
}
pub unsafe fn l_Lake_Toml_skipFn(
    mut v_x_1735_: *mut crate::leanh::LeanObject,
    mut v_s_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1736_);
    return v_s_1736_;
}
pub unsafe fn l_Lake_Toml_skipFn___boxed(
    mut v_x_1737_: *mut crate::leanh::LeanObject,
    mut v_s_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lake_Toml_skipFn(v_x_1737_, v_s_1738_);
    crate::leanh::lean_dec_ref(v_s_1738_);
    crate::leanh::lean_dec_ref(v_x_1737_);
    return v_res_1739_;
}
pub unsafe fn l_Lake_Toml_instAndThenParserFn__lake___lam__0(
    mut v_p_1741_: *mut crate::leanh::LeanObject,
    mut v_q_1742_: *mut crate::leanh::LeanObject,
    mut v_c_1743_: *mut crate::leanh::LeanObject,
    mut v_s_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: u8 = 0;
    crate::leanh::lean_inc_ref(v_c_1743_);
    v_s_1745_ = crate::leanh::lean_apply_2(v_p_1741_, v_c_1743_, v_s_1744_);
    v_errorMsg_1746_ = crate::leanh::lean_ctor_get(v_s_1745_, 4);
    crate::leanh::lean_inc(v_errorMsg_1746_);
    v___x_1747_ = l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
    v___x_1748_ = crate::leanh::lean_box(0);
    v___x_1749_ = l_Option_instBEq_beq___redArg(v___x_1747_, v_errorMsg_1746_, v___x_1748_);
    if v___x_1749_ == 0 {
        crate::leanh::lean_dec_ref(v_c_1743_);
        crate::leanh::lean_dec_ref(v_q_1742_);
        return v_s_1745_;
    } else {
        let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1750_ = crate::leanh::lean_box(0);
        v___x_1751_ = crate::leanh::lean_apply_3(v_q_1742_, v___x_1750_, v_c_1743_, v_s_1745_);
        return v___x_1751_;
    }
}
pub unsafe fn l_Lake_Toml_usePosFn(
    mut v_f_1754_: *mut crate::leanh::LeanObject,
    mut v_c_1755_: *mut crate::leanh::LeanObject,
    mut v_s_1756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_1757_ = crate::leanh::lean_ctor_get(v_s_1756_, 2);
    crate::leanh::lean_inc(v_pos_1757_);
    v___x_1758_ = crate::leanh::lean_apply_3(v_f_1754_, v_pos_1757_, v_c_1755_, v_s_1756_);
    return v___x_1758_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(
    mut v_x_1759_: *mut crate::leanh::LeanObject,
    mut v_x_1760_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1759_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_1760_) == 0 {
            let mut v___x_1761_: u8 = 0;
            v___x_1761_ = 1;
            return v___x_1761_;
        } else {
            let mut v___x_1762_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1760_, 1);
            v___x_1762_ = 0;
            return v___x_1762_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_1760_) == 0 {
            let mut v___x_1763_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_x_1759_, 1);
            v___x_1763_ = 0;
            return v___x_1763_;
        } else {
            let mut v_val_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: u8 = 0;
            v_val_1764_ = crate::leanh::lean_ctor_get(v_x_1759_, 0);
            crate::leanh::lean_inc(v_val_1764_);
            crate::leanh::lean_dec_ref_known(v_x_1759_, 1);
            v_val_1765_ = crate::leanh::lean_ctor_get(v_x_1760_, 0);
            crate::leanh::lean_inc(v_val_1765_);
            crate::leanh::lean_dec_ref_known(v_x_1760_, 1);
            v___x_1766_ = l_Lean_Parser_instBEqError_beq(v_val_1764_, v_val_1765_);
            return v___x_1766_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0___boxed(
    mut v_x_1767_: *mut crate::leanh::LeanObject,
    mut v_x_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: u8 = 0;
    let mut v_r_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_x_1767_, v_x_1768_);
    v_r_1770_ = crate::leanh::lean_box((v_res_1769_) as usize);
    return v_r_1770_;
}
pub unsafe fn l_Lake_Toml_optFn(
    mut v_p_1771_: *mut crate::leanh::LeanObject,
    mut v_c_1772_: *mut crate::leanh::LeanObject,
    mut v_s_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_iniSz_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    v_pos_1774_ = crate::leanh::lean_ctor_get(v_s_1773_, 2);
    crate::leanh::lean_inc(v_pos_1774_);
    v_iniSz_1775_ = l_Lean_Parser_ParserState_stackSize(v_s_1773_);
    v_s_1776_ = crate::leanh::lean_apply_2(v_p_1771_, v_c_1772_, v_s_1773_);
    v_pos_1777_ = crate::leanh::lean_ctor_get(v_s_1776_, 2);
    crate::leanh::lean_inc(v_pos_1777_);
    v_errorMsg_1778_ = crate::leanh::lean_ctor_get(v_s_1776_, 4);
    crate::leanh::lean_inc(v_errorMsg_1778_);
    v___x_1779_ = crate::leanh::lean_box(0);
    v___x_1780_ =
        l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_1778_, v___x_1779_);
    if v___x_1780_ == 0 {
        let mut v___x_1781_: u8 = 0;
        v___x_1781_ = lean_nat_dec_eq(v_pos_1777_, v_pos_1774_);
        crate::leanh::lean_dec(v_pos_1777_);
        if v___x_1781_ == 0 {
            crate::leanh::lean_dec(v_iniSz_1775_);
            crate::leanh::lean_dec(v_pos_1774_);
            return v_s_1776_;
        } else {
            let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1782_ = l_Lean_Parser_ParserState_restore(v_s_1776_, v_iniSz_1775_, v_pos_1774_);
            crate::leanh::lean_dec(v_iniSz_1775_);
            return v___x_1782_;
        }
    } else {
        crate::leanh::lean_dec(v_pos_1777_);
        crate::leanh::lean_dec(v_iniSz_1775_);
        crate::leanh::lean_dec(v_pos_1774_);
        return v_s_1776_;
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(
    mut v_p_1783_: *mut crate::leanh::LeanObject,
    mut v_c_1784_: *mut crate::leanh::LeanObject,
    mut v_x_1785_: *mut crate::leanh::LeanObject,
    mut v_x_1786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1788_: u8 = 0;
    let mut v_s_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_one_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1787_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1788_ = lean_nat_dec_eq(v_x_1785_, v_zero_1787_);
                if v_isZero_1788_ == 1 {
                    crate::leanh::lean_dec(v_x_1785_);
                    crate::leanh::lean_dec_ref(v_c_1784_);
                    crate::leanh::lean_dec_ref(v_p_1783_);
                    return v_x_1786_;
                } else {
                    crate::leanh::lean_inc_ref(v_p_1783_);
                    crate::leanh::lean_inc_ref(v_c_1784_);
                    v_s_1789_ = crate::leanh::lean_apply_2(v_p_1783_, v_c_1784_, v_x_1786_);
                    v_errorMsg_1790_ = crate::leanh::lean_ctor_get(v_s_1789_, 4);
                    crate::leanh::lean_inc(v_errorMsg_1790_);
                    v___x_1791_ = l_Lake_Toml_instAndThenParserFn__lake___lam__0___closed__0;
                    v___x_1792_ = crate::leanh::lean_box(0);
                    v___x_1793_ =
                        l_Option_instBEq_beq___redArg(v___x_1791_, v_errorMsg_1790_, v___x_1792_);
                    if v___x_1793_ == 0 {
                        crate::leanh::lean_dec(v_x_1785_);
                        crate::leanh::lean_dec_ref(v_c_1784_);
                        crate::leanh::lean_dec_ref(v_p_1783_);
                        return v_s_1789_;
                    } else {
                        v_one_1794_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1795_ = lean_nat_sub(v_x_1785_, v_one_1794_);
                        crate::leanh::lean_dec(v_x_1785_);
                        v_x_1785_ = v_n_1795_;
                        v_x_1786_ = v_s_1789_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_repeatFn(
    mut v_n_1797_: *mut crate::leanh::LeanObject,
    mut v_p_1798_: *mut crate::leanh::LeanObject,
    mut v_c_1799_: *mut crate::leanh::LeanObject,
    mut v_s_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop(
        v_p_1798_, v_c_1799_, v_n_1797_, v_s_1800_,
    );
    return v___x_1801_;
}
pub unsafe fn l_Lake_Toml_mkUnexpectedCharError(
    mut v_s_1805_: *mut crate::leanh::LeanObject,
    mut v_c_1806_: u32,
    mut v_expected_1807_: *mut crate::leanh::LeanObject,
    mut v_pushMissing_1808_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = l_Lake_Toml_mkUnexpectedCharError___closed__0;
    v___x_1810_ = l_Lake_Toml_mkUnexpectedCharError___closed__1;
    v___x_1811_ = lean_string_push(v___x_1810_, v_c_1806_);
    v___x_1812_ = lean_string_append(v___x_1809_, v___x_1811_);
    crate::leanh::lean_dec_ref(v___x_1811_);
    v___x_1813_ = l_Lake_Toml_mkUnexpectedCharError___closed__2;
    v___x_1814_ = lean_string_append(v___x_1812_, v___x_1813_);
    v___x_1815_ = l_Lean_Parser_ParserState_mkUnexpectedError(
        v_s_1805_,
        v___x_1814_,
        v_expected_1807_,
        v_pushMissing_1808_,
    );
    return v___x_1815_;
}
pub unsafe fn l_Lake_Toml_mkUnexpectedCharError___boxed(
    mut v_s_1816_: *mut crate::leanh::LeanObject,
    mut v_c_1817_: *mut crate::leanh::LeanObject,
    mut v_expected_1818_: *mut crate::leanh::LeanObject,
    mut v_pushMissing_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1820_: u32 = 0;
    let mut v_pushMissing_boxed_1821_: u8 = 0;
    let mut v_res_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1820_ = crate::leanh::lean_unbox_uint32(v_c_1817_);
    crate::leanh::lean_dec(v_c_1817_);
    v_pushMissing_boxed_1821_ = (crate::leanh::lean_unbox(v_pushMissing_1819_) as u8);
    v_res_1822_ = l_Lake_Toml_mkUnexpectedCharError(
        v_s_1816_,
        v_c_boxed_1820_,
        v_expected_1818_,
        v_pushMissing_boxed_1821_,
    );
    return v_res_1822_;
}
pub unsafe fn l_Lake_Toml_satisfyFn(
    mut v_p_1823_: *mut crate::leanh::LeanObject,
    mut v_expected_1824_: *mut crate::leanh::LeanObject,
    mut v_c_1825_: *mut crate::leanh::LeanObject,
    mut v_s_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    v_pos_1827_ = crate::leanh::lean_ctor_get(v_s_1826_, 2);
    v_toInputContext_1828_ = crate::leanh::lean_ctor_get(v_c_1825_, 0);
    v___x_1829_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1828_, v_pos_1827_);
    if v___x_1829_ == 0 {
        let mut v_inputString_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_curr_1831_: u32 = 0;
        let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1834_: u8 = 0;
        v_inputString_1830_ = crate::leanh::lean_ctor_get(v_toInputContext_1828_, 0);
        v_curr_1831_ = lean_string_utf8_get_fast(v_inputString_1830_, v_pos_1827_);
        v___x_1832_ = crate::leanh::lean_box_uint32(v_curr_1831_);
        v___x_1833_ = crate::leanh::lean_apply_1(v_p_1823_, v___x_1832_);
        v___x_1834_ = (crate::leanh::lean_unbox(v___x_1833_) as u8);
        if v___x_1834_ == 0 {
            let mut v___x_1835_: u8 = 0;
            let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1835_ = 1;
            v___x_1836_ = l_Lake_Toml_mkUnexpectedCharError(
                v_s_1826_,
                v_curr_1831_,
                v_expected_1824_,
                v___x_1835_,
            );
            return v___x_1836_;
        } else {
            let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_pos_1827_);
            crate::leanh::lean_dec(v_expected_1824_);
            v___x_1837_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_s_1826_, v_c_1825_, v_pos_1827_);
            crate::leanh::lean_dec(v_pos_1827_);
            return v___x_1837_;
        }
    } else {
        let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_p_1823_);
        v___x_1838_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1826_, v_expected_1824_);
        return v___x_1838_;
    }
}
pub unsafe fn l_Lake_Toml_satisfyFn___boxed(
    mut v_p_1839_: *mut crate::leanh::LeanObject,
    mut v_expected_1840_: *mut crate::leanh::LeanObject,
    mut v_c_1841_: *mut crate::leanh::LeanObject,
    mut v_s_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lake_Toml_satisfyFn(v_p_1839_, v_expected_1840_, v_c_1841_, v_s_1842_);
    crate::leanh::lean_dec_ref(v_c_1841_);
    return v_res_1843_;
}
pub unsafe fn l_Lake_Toml_takeWhile1Fn(
    mut v_p_1844_: *mut crate::leanh::LeanObject,
    mut v_expected_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
    mut v_a_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v_inputString_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_1858_: u32 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: u8 = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_1854_ = crate::leanh::lean_ctor_get(v_a_1847_, 2);
                v_toInputContext_1855_ = crate::leanh::lean_ctor_get(v_a_1846_, 0);
                v___x_1856_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1855_, v_pos_1854_);
                if v___x_1856_ == 0 {
                    v_inputString_1857_ = crate::leanh::lean_ctor_get(v_toInputContext_1855_, 0);
                    v_curr_1858_ = lean_string_utf8_get_fast(v_inputString_1857_, v_pos_1854_);
                    v___x_1859_ = crate::leanh::lean_box_uint32(v_curr_1858_);
                    crate::leanh::lean_inc_ref(v_p_1844_);
                    v___x_1860_ = crate::leanh::lean_apply_1(v_p_1844_, v___x_1859_);
                    v___x_1861_ = (crate::leanh::lean_unbox(v___x_1860_) as u8);
                    if v___x_1861_ == 0 {
                        v___x_1862_ = 1;
                        v___x_1863_ = l_Lake_Toml_mkUnexpectedCharError(
                            v_a_1847_,
                            v_curr_1858_,
                            v_expected_1845_,
                            v___x_1862_,
                        );
                        v___y_1849_ = v___x_1863_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1854_);
                        crate::leanh::lean_dec(v_expected_1845_);
                        v___x_1864_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_a_1847_,
                            v_a_1846_,
                            v_pos_1854_,
                        );
                        crate::leanh::lean_dec(v_pos_1854_);
                        v___y_1849_ = v___x_1864_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1865_ = l_Lean_Parser_ParserState_mkEOIError(v_a_1847_, v_expected_1845_);
                    v___y_1849_ = v___x_1865_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_errorMsg_1850_ = crate::leanh::lean_ctor_get(v___y_1849_, 4);
                v___x_1851_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_errorMsg_1850_);
                v___x_1852_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(
                    v_errorMsg_1850_,
                    v___x_1851_,
                );
                if v___x_1852_ == 0 {
                    crate::leanh::lean_dec_ref(v_p_1844_);
                    return v___y_1849_;
                } else {
                    v___x_1853_ = l_Lean_Parser_takeWhileFn(v_p_1844_, v_a_1846_, v___y_1849_);
                    return v___x_1853_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_takeWhile1Fn___boxed(
    mut v_p_1866_: *mut crate::leanh::LeanObject,
    mut v_expected_1867_: *mut crate::leanh::LeanObject,
    mut v_a_1868_: *mut crate::leanh::LeanObject,
    mut v_a_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1870_ = l_Lake_Toml_takeWhile1Fn(v_p_1866_, v_expected_1867_, v_a_1868_, v_a_1869_);
    crate::leanh::lean_dec_ref(v_a_1868_);
    return v_res_1870_;
}
pub unsafe fn l_Lake_Toml_digitFn(
    mut v_expected_1871_: *mut crate::leanh::LeanObject,
    mut v_a_1872_: *mut crate::leanh::LeanObject,
    mut v_a_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: u8 = 0;
    let mut v_inputString_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_1878_: u32 = 0;
    let mut v___y_1880_: u8 = 0;
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: u32 = 0;
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: u32 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_1874_ = crate::leanh::lean_ctor_get(v_a_1873_, 2);
                v_toInputContext_1875_ = crate::leanh::lean_ctor_get(v_a_1872_, 0);
                v___x_1876_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1875_, v_pos_1874_);
                if v___x_1876_ == 0 {
                    v_inputString_1877_ = crate::leanh::lean_ctor_get(v_toInputContext_1875_, 0);
                    v_curr_1878_ = lean_string_utf8_get_fast(v_inputString_1877_, v_pos_1874_);
                    v___x_1884_ = 48;
                    v___x_1885_ = lean_uint32_dec_le(v___x_1884_, v_curr_1878_);
                    if v___x_1885_ == 0 {
                        v___y_1880_ = v___x_1885_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1886_ = 57;
                        v___x_1887_ = lean_uint32_dec_le(v_curr_1878_, v___x_1886_);
                        v___y_1880_ = v___x_1887_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1888_ = l_Lean_Parser_ParserState_mkEOIError(v_a_1873_, v_expected_1871_);
                    return v___x_1888_;
                }
            }
            1 => {
                if v___y_1880_ == 0 {
                    v___x_1881_ = 1;
                    v___x_1882_ = l_Lake_Toml_mkUnexpectedCharError(
                        v_a_1873_,
                        v_curr_1878_,
                        v_expected_1871_,
                        v___x_1881_,
                    );
                    return v___x_1882_;
                } else {
                    crate::leanh::lean_inc(v_pos_1874_);
                    crate::leanh::lean_dec(v_expected_1871_);
                    v___x_1883_ = l_Lean_Parser_ParserState_next_x27___redArg(
                        v_a_1873_,
                        v_a_1872_,
                        v_pos_1874_,
                    );
                    crate::leanh::lean_dec(v_pos_1874_);
                    return v___x_1883_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_digitFn___boxed(
    mut v_expected_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1892_ = l_Lake_Toml_digitFn(v_expected_1889_, v_a_1890_, v_a_1891_);
    crate::leanh::lean_dec_ref(v_a_1890_);
    return v_res_1892_;
}
pub unsafe fn l_Lake_Toml_digitPairFn(
    mut v_expected_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    crate::leanh::lean_inc(v_expected_1893_);
    v_s_1896_ = l_Lake_Toml_digitFn(v_expected_1893_, v_a_1894_, v_a_1895_);
    v_errorMsg_1897_ = crate::leanh::lean_ctor_get(v_s_1896_, 4);
    crate::leanh::lean_inc(v_errorMsg_1897_);
    v___x_1898_ = crate::leanh::lean_box(0);
    v___x_1899_ =
        l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_1897_, v___x_1898_);
    if v___x_1899_ == 0 {
        crate::leanh::lean_dec(v_expected_1893_);
        return v_s_1896_;
    } else {
        let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1900_ = l_Lake_Toml_digitFn(v_expected_1893_, v_a_1894_, v_s_1896_);
        return v___x_1900_;
    }
}
pub unsafe fn l_Lake_Toml_digitPairFn___boxed(
    mut v_expected_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l_Lake_Toml_digitPairFn(v_expected_1901_, v_a_1902_, v_a_1903_);
    crate::leanh::lean_dec_ref(v_a_1902_);
    return v_res_1904_;
}
pub unsafe fn l_Lake_Toml_chFn(
    mut v_c_1905_: u32,
    mut v_expected_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    v_pos_1909_ = crate::leanh::lean_ctor_get(v_a_1908_, 2);
    v_toInputContext_1910_ = crate::leanh::lean_ctor_get(v_a_1907_, 0);
    v___x_1911_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1910_, v_pos_1909_);
    if v___x_1911_ == 0 {
        let mut v_inputString_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_curr_1913_: u32 = 0;
        let mut v___x_1914_: u8 = 0;
        v_inputString_1912_ = crate::leanh::lean_ctor_get(v_toInputContext_1910_, 0);
        v_curr_1913_ = lean_string_utf8_get_fast(v_inputString_1912_, v_pos_1909_);
        v___x_1914_ = lean_uint32_dec_eq(v_curr_1913_, v_c_1905_);
        if v___x_1914_ == 0 {
            let mut v___x_1915_: u8 = 0;
            let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1915_ = 1;
            v___x_1916_ = l_Lake_Toml_mkUnexpectedCharError(
                v_a_1908_,
                v_curr_1913_,
                v_expected_1906_,
                v___x_1915_,
            );
            return v___x_1916_;
        } else {
            let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_pos_1909_);
            crate::leanh::lean_dec(v_expected_1906_);
            v___x_1917_ =
                l_Lean_Parser_ParserState_next_x27___redArg(v_a_1908_, v_a_1907_, v_pos_1909_);
            crate::leanh::lean_dec(v_pos_1909_);
            return v___x_1917_;
        }
    } else {
        let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1918_ = l_Lean_Parser_ParserState_mkEOIError(v_a_1908_, v_expected_1906_);
        return v___x_1918_;
    }
}
pub unsafe fn l_Lake_Toml_chFn___boxed(
    mut v_c_1919_: *mut crate::leanh::LeanObject,
    mut v_expected_1920_: *mut crate::leanh::LeanObject,
    mut v_a_1921_: *mut crate::leanh::LeanObject,
    mut v_a_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1923_: u32 = 0;
    let mut v_res_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1923_ = crate::leanh::lean_unbox_uint32(v_c_1919_);
    crate::leanh::lean_dec(v_c_1919_);
    v_res_1924_ = l_Lake_Toml_chFn(v_c_boxed_1923_, v_expected_1920_, v_a_1921_, v_a_1922_);
    crate::leanh::lean_dec_ref(v_a_1921_);
    return v_res_1924_;
}
pub unsafe fn l_Lake_Toml_strAuxFn(
    mut v_str_1925_: *mut crate::leanh::LeanObject,
    mut v_expected_1926_: *mut crate::leanh::LeanObject,
    mut v_strPos_1927_: *mut crate::leanh::LeanObject,
    mut v_c_1928_: *mut crate::leanh::LeanObject,
    mut v_s_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1930_: u8 = 0;
    let mut v___x_1931_: u32 = 0;
    let mut v_s_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1930_ = lean_string_utf8_at_end(v_str_1925_, v_strPos_1927_);
                if v___x_1930_ == 0 {
                    v___x_1931_ = lean_string_utf8_get_fast(v_str_1925_, v_strPos_1927_);
                    crate::leanh::lean_inc(v_expected_1926_);
                    v_s_1932_ =
                        l_Lake_Toml_chFn(v___x_1931_, v_expected_1926_, v_c_1928_, v_s_1929_);
                    v_errorMsg_1933_ = crate::leanh::lean_ctor_get(v_s_1932_, 4);
                    crate::leanh::lean_inc(v_errorMsg_1933_);
                    v___x_1934_ = crate::leanh::lean_box(0);
                    v___x_1935_ = l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(
                        v_errorMsg_1933_,
                        v___x_1934_,
                    );
                    if v___x_1935_ == 0 {
                        crate::leanh::lean_dec(v_strPos_1927_);
                        crate::leanh::lean_dec(v_expected_1926_);
                        return v_s_1932_;
                    } else {
                        if v___x_1930_ == 0 {
                            v___x_1936_ = lean_string_utf8_next_fast(v_str_1925_, v_strPos_1927_);
                            crate::leanh::lean_dec(v_strPos_1927_);
                            v_strPos_1927_ = v___x_1936_;
                            v_s_1929_ = v_s_1932_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_strPos_1927_);
                            crate::leanh::lean_dec(v_expected_1926_);
                            return v_s_1932_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_strPos_1927_);
                    crate::leanh::lean_dec(v_expected_1926_);
                    return v_s_1929_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_strAuxFn___boxed(
    mut v_str_1938_: *mut crate::leanh::LeanObject,
    mut v_expected_1939_: *mut crate::leanh::LeanObject,
    mut v_strPos_1940_: *mut crate::leanh::LeanObject,
    mut v_c_1941_: *mut crate::leanh::LeanObject,
    mut v_s_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lake_Toml_strAuxFn(
        v_str_1938_,
        v_expected_1939_,
        v_strPos_1940_,
        v_c_1941_,
        v_s_1942_,
    );
    crate::leanh::lean_dec_ref(v_c_1941_);
    crate::leanh::lean_dec_ref(v_str_1938_);
    return v_res_1943_;
}
pub unsafe fn l_Lake_Toml_strFn(
    mut v_str_1944_: *mut crate::leanh::LeanObject,
    mut v_expected_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
    mut v_a_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1949_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_strAuxFn___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1949_, 0, v_str_1944_);
    crate::leanh::lean_closure_set(v___x_1949_, 1, v_expected_1945_);
    crate::leanh::lean_closure_set(v___x_1949_, 2, v___x_1948_);
    v___x_1950_ = l_Lean_Parser_atomicFn(v___x_1949_, v_a_1946_, v_a_1947_);
    return v___x_1950_;
}
pub unsafe fn l_Lake_Toml_sepByChar1Fn(
    mut v_p_1952_: *mut crate::leanh::LeanObject,
    mut v_sep_1953_: u32,
    mut v_expected_1954_: *mut crate::leanh::LeanObject,
    mut v_c_1955_: *mut crate::leanh::LeanObject,
    mut v_s_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    v_pos_1957_ = crate::leanh::lean_ctor_get(v_s_1956_, 2);
    v_toInputContext_1958_ = crate::leanh::lean_ctor_get(v_c_1955_, 0);
    v___x_1959_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1958_, v_pos_1957_);
    if v___x_1959_ == 0 {
        let mut v_inputString_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_curr_1961_: u32 = 0;
        let mut v_s_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1965_: u8 = 0;
        crate::leanh::lean_inc(v_pos_1957_);
        v_inputString_1960_ = crate::leanh::lean_ctor_get(v_toInputContext_1958_, 0);
        v_curr_1961_ = lean_string_utf8_get_fast(v_inputString_1960_, v_pos_1957_);
        v_s_1962_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1956_, v_c_1955_, v_pos_1957_);
        crate::leanh::lean_dec(v_pos_1957_);
        v___x_1963_ = crate::leanh::lean_box_uint32(v_curr_1961_);
        crate::leanh::lean_inc_ref(v_p_1952_);
        v___x_1964_ = crate::leanh::lean_apply_1(v_p_1952_, v___x_1963_);
        v___x_1965_ = (crate::leanh::lean_unbox(v___x_1964_) as u8);
        if v___x_1965_ == 0 {
            let mut v___x_1966_: u8 = 0;
            let mut v___x_1967_: u8 = 0;
            crate::leanh::lean_dec_ref(v_p_1952_);
            v___x_1966_ = 1;
            v___x_1967_ = lean_uint32_dec_eq(v_curr_1961_, v_sep_1953_);
            if v___x_1967_ == 0 {
                let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1968_ = l_Lake_Toml_mkUnexpectedCharError(
                    v_s_1962_,
                    v_curr_1961_,
                    v_expected_1954_,
                    v___x_1966_,
                );
                return v___x_1968_;
            } else {
                let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1969_ = l_Lake_Toml_sepByChar1Fn___closed__0;
                v___x_1970_ = l_Lake_Toml_mkUnexpectedCharError___closed__1;
                v___x_1971_ = lean_string_push(v___x_1970_, v_curr_1961_);
                v___x_1972_ = lean_string_append(v___x_1969_, v___x_1971_);
                crate::leanh::lean_dec_ref(v___x_1971_);
                v___x_1973_ = l_Lake_Toml_mkUnexpectedCharError___closed__2;
                v___x_1974_ = lean_string_append(v___x_1972_, v___x_1973_);
                v___x_1975_ = l_Lean_Parser_ParserState_mkUnexpectedError(
                    v_s_1962_,
                    v___x_1974_,
                    v_expected_1954_,
                    v___x_1966_,
                );
                return v___x_1975_;
            }
        } else {
            let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1976_ = l_Lake_Toml_sepByChar1AuxFn(
                v_p_1952_,
                v_sep_1953_,
                v_expected_1954_,
                v_c_1955_,
                v_s_1962_,
            );
            return v___x_1976_;
        }
    } else {
        crate::leanh::lean_dec(v_expected_1954_);
        crate::leanh::lean_dec_ref(v_p_1952_);
        return v_s_1956_;
    }
}
pub unsafe fn l_Lake_Toml_sepByChar1AuxFn(
    mut v_p_1977_: *mut crate::leanh::LeanObject,
    mut v_sep_1978_: u32,
    mut v_expected_1979_: *mut crate::leanh::LeanObject,
    mut v_c_1980_: *mut crate::leanh::LeanObject,
    mut v_s_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toInputContext_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v_inputString_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_1986_: u32 = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: u8 = 0;
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_1982_ = crate::leanh::lean_ctor_get(v_s_1981_, 2);
                v_toInputContext_1983_ = crate::leanh::lean_ctor_get(v_c_1980_, 0);
                v___x_1984_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1983_, v_pos_1982_);
                if v___x_1984_ == 0 {
                    v_inputString_1985_ = crate::leanh::lean_ctor_get(v_toInputContext_1983_, 0);
                    v_curr_1986_ = lean_string_utf8_get_fast(v_inputString_1985_, v_pos_1982_);
                    v___x_1987_ = crate::leanh::lean_box_uint32(v_curr_1986_);
                    crate::leanh::lean_inc_ref(v_p_1977_);
                    v___x_1988_ = crate::leanh::lean_apply_1(v_p_1977_, v___x_1987_);
                    v___x_1989_ = (crate::leanh::lean_unbox(v___x_1988_) as u8);
                    if v___x_1989_ == 0 {
                        v___x_1990_ = lean_uint32_dec_eq(v_curr_1986_, v_sep_1978_);
                        if v___x_1990_ == 0 {
                            crate::leanh::lean_dec(v_expected_1979_);
                            crate::leanh::lean_dec_ref(v_p_1977_);
                            return v_s_1981_;
                        } else {
                            crate::leanh::lean_inc(v_pos_1982_);
                            v___x_1991_ = l_Lean_Parser_ParserState_next_x27___redArg(
                                v_s_1981_,
                                v_c_1980_,
                                v_pos_1982_,
                            );
                            crate::leanh::lean_dec(v_pos_1982_);
                            v___x_1992_ = l_Lake_Toml_sepByChar1Fn(
                                v_p_1977_,
                                v_sep_1978_,
                                v_expected_1979_,
                                v_c_1980_,
                                v___x_1991_,
                            );
                            return v___x_1992_;
                        }
                    } else {
                        crate::leanh::lean_inc(v_pos_1982_);
                        v___x_1993_ = l_Lean_Parser_ParserState_next_x27___redArg(
                            v_s_1981_,
                            v_c_1980_,
                            v_pos_1982_,
                        );
                        crate::leanh::lean_dec(v_pos_1982_);
                        v_s_1981_ = v___x_1993_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_expected_1979_);
                    crate::leanh::lean_dec_ref(v_p_1977_);
                    return v_s_1981_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_sepByChar1AuxFn___boxed(
    mut v_p_1995_: *mut crate::leanh::LeanObject,
    mut v_sep_1996_: *mut crate::leanh::LeanObject,
    mut v_expected_1997_: *mut crate::leanh::LeanObject,
    mut v_c_1998_: *mut crate::leanh::LeanObject,
    mut v_s_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sep_boxed_2000_: u32 = 0;
    let mut v_res_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sep_boxed_2000_ = crate::leanh::lean_unbox_uint32(v_sep_1996_);
    crate::leanh::lean_dec(v_sep_1996_);
    v_res_2001_ = l_Lake_Toml_sepByChar1AuxFn(
        v_p_1995_,
        v_sep_boxed_2000_,
        v_expected_1997_,
        v_c_1998_,
        v_s_1999_,
    );
    crate::leanh::lean_dec_ref(v_c_1998_);
    return v_res_2001_;
}
pub unsafe fn l_Lake_Toml_sepByChar1Fn___boxed(
    mut v_p_2002_: *mut crate::leanh::LeanObject,
    mut v_sep_2003_: *mut crate::leanh::LeanObject,
    mut v_expected_2004_: *mut crate::leanh::LeanObject,
    mut v_c_2005_: *mut crate::leanh::LeanObject,
    mut v_s_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sep_boxed_2007_: u32 = 0;
    let mut v_res_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sep_boxed_2007_ = crate::leanh::lean_unbox_uint32(v_sep_2003_);
    crate::leanh::lean_dec(v_sep_2003_);
    v_res_2008_ = l_Lake_Toml_sepByChar1Fn(
        v_p_2002_,
        v_sep_boxed_2007_,
        v_expected_2004_,
        v_c_2005_,
        v_s_2006_,
    );
    crate::leanh::lean_dec_ref(v_c_2005_);
    return v_res_2008_;
}
pub unsafe fn l_Lake_Toml_pushAtom(
    mut v_startPos_2009_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2010_: *mut crate::leanh::LeanObject,
    mut v_c_2011_: *mut crate::leanh::LeanObject,
    mut v_s_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInputContext_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v_leading_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_atom_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_unused_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2013_ = crate::leanh::lean_ctor_get(v_c_2011_, 0);
                crate::leanh::lean_inc_ref(v_toInputContext_2013_);
                v_pos_2014_ = crate::leanh::lean_ctor_get(v_s_2012_, 2);
                crate::leanh::lean_inc(v_pos_2014_);
                v_inputString_2015_ = crate::leanh::lean_ctor_get(v_toInputContext_2013_, 0);
                v_endPos_2016_ = crate::leanh::lean_ctor_get(v_toInputContext_2013_, 3);
                v_isSharedCheck_2036_ =
                    (!crate::leanh::lean_is_exclusive(v_toInputContext_2013_)) as u8;
                if v_isSharedCheck_2036_ == 0 {
                    v_unused_2037_ = crate::leanh::lean_ctor_get(v_toInputContext_2013_, 2);
                    crate::leanh::lean_dec(v_unused_2037_);
                    v_unused_2038_ = crate::leanh::lean_ctor_get(v_toInputContext_2013_, 1);
                    crate::leanh::lean_dec(v_unused_2038_);
                    v___x_2018_ = v_toInputContext_2013_;
                    v_isShared_2019_ = v_isSharedCheck_2036_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endPos_2016_);
                    crate::leanh::lean_inc(v_inputString_2015_);
                    crate::leanh::lean_dec(v_toInputContext_2013_);
                    v___x_2018_ = crate::leanh::lean_box(0);
                    v_isShared_2019_ = v_isSharedCheck_2036_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_startPos_2009_);
                v_leading_2020_ =
                    l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2011_, v_startPos_2009_);
                v_s_2021_ = crate::leanh::lean_apply_2(v_trailingFn_2010_, v_c_2011_, v_s_2012_);
                v_pos_2022_ = crate::leanh::lean_ctor_get(v_s_2021_, 2);
                crate::leanh::lean_inc(v_pos_2022_);
                v_val_2023_ =
                    lean_string_utf8_extract(v_inputString_2015_, v_startPos_2009_, v_pos_2014_);
                v___x_2033_ = lean_nat_dec_le(v_pos_2022_, v_endPos_2016_);
                if v___x_2033_ == 0 {
                    crate::leanh::lean_dec(v_pos_2022_);
                    v___x_2034_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2034_, 0, v_inputString_2015_);
                    crate::leanh::lean_ctor_set(v___x_2034_, 1, v_pos_2014_);
                    crate::leanh::lean_ctor_set(v___x_2034_, 2, v_endPos_2016_);
                    v___y_2025_ = v___x_2034_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_endPos_2016_);
                    v___x_2035_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2035_, 0, v_inputString_2015_);
                    crate::leanh::lean_ctor_set(v___x_2035_, 1, v_pos_2014_);
                    crate::leanh::lean_ctor_set(v___x_2035_, 2, v_pos_2022_);
                    v___y_2025_ = v___x_2035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2026_ = lean_string_utf8_byte_size(v_val_2023_);
                v___x_2027_ = lean_nat_add(v_startPos_2009_, v___x_2026_);
                if v_isShared_2019_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2018_, 3, v___x_2027_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 2, v___y_2025_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 1, v_startPos_2009_);
                    crate::leanh::lean_ctor_set(v___x_2018_, 0, v_leading_2020_);
                    v___x_2029_ = v___x_2018_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_leading_2020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_startPos_2009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 2, v___y_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 3, v___x_2027_);
                    v___x_2029_ = v_reuseFailAlloc_2032_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_atom_2030_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_atom_2030_, 0, v___x_2029_);
                crate::leanh::lean_ctor_set(v_atom_2030_, 1, v_val_2023_);
                v___x_2031_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2021_, v_atom_2030_);
                return v___x_2031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_atomFn(
    mut v_p_2039_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2040_: *mut crate::leanh::LeanObject,
    mut v_c_2041_: *mut crate::leanh::LeanObject,
    mut v_s_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: u8 = 0;
    v_pos_2043_ = crate::leanh::lean_ctor_get(v_s_2042_, 2);
    crate::leanh::lean_inc(v_pos_2043_);
    crate::leanh::lean_inc_ref(v_c_2041_);
    v_s_2044_ = crate::leanh::lean_apply_2(v_p_2039_, v_c_2041_, v_s_2042_);
    v_errorMsg_2045_ = crate::leanh::lean_ctor_get(v_s_2044_, 4);
    crate::leanh::lean_inc(v_errorMsg_2045_);
    v___x_2046_ = crate::leanh::lean_box(0);
    v___x_2047_ =
        l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_2045_, v___x_2046_);
    if v___x_2047_ == 0 {
        crate::leanh::lean_dec(v_pos_2043_);
        crate::leanh::lean_dec_ref(v_c_2041_);
        crate::leanh::lean_dec_ref(v_trailingFn_2040_);
        return v_s_2044_;
    } else {
        let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2048_ = l_Lake_Toml_pushAtom(v_pos_2043_, v_trailingFn_2040_, v_c_2041_, v_s_2044_);
        return v___x_2048_;
    }
}
pub unsafe fn l_Lake_Toml_atom___lam__0(
    mut v___y_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_2049_);
    return v___y_2049_;
}
pub unsafe fn l_Lake_Toml_atom___lam__0___boxed(
    mut v___y_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Lake_Toml_atom___lam__0(v___y_2050_);
    crate::leanh::lean_dec(v___y_2050_);
    return v_res_2051_;
}
pub unsafe fn l_Lake_Toml_atom___lam__1(
    mut v___y_2052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_2052_);
    return v___y_2052_;
}
pub unsafe fn l_Lake_Toml_atom___lam__1___boxed(
    mut v___y_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2054_ = l_Lake_Toml_atom___lam__1(v___y_2053_);
    crate::leanh::lean_dec_ref(v___y_2053_);
    return v_res_2054_;
}
pub unsafe fn l_Lake_Toml_atom(
    mut v_p_2061_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l_Lake_Toml_atom___closed__2;
    v___x_2064_ =
        crate::leanh::lean_alloc_closure(l_Lake_Toml_atomFn as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2064_, 0, v_p_2061_);
    crate::leanh::lean_closure_set(v___x_2064_, 1, v_trailingFn_2062_);
    v___x_2065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_2063_);
    crate::leanh::lean_ctor_set(v___x_2065_, 1, v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(
    mut v___y_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2068_ = lean_st_ref_get(v___y_2066_);
    v_stxTrav_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
    crate::leanh::lean_inc_ref(v_stxTrav_2069_);
    crate::leanh::lean_dec(v___x_2068_);
    v_cur_2070_ = crate::leanh::lean_ctor_get(v_stxTrav_2069_, 0);
    crate::leanh::lean_inc(v_cur_2070_);
    crate::leanh::lean_dec_ref(v_stxTrav_2069_);
    v___x_2071_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2071_, 0, v_cur_2070_);
    return v___x_2071_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg___boxed(
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2074_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(
            v___y_2072_,
        );
    crate::leanh::lean_dec(v___y_2072_);
    return v_res_2074_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(
    mut v___y_2075_: *mut crate::leanh::LeanObject,
    mut v___y_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(
            v___y_2076_,
        );
    return v___x_2080_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___boxed(
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2086_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0(
        v___y_2081_,
        v___y_2082_,
        v___y_2083_,
        v___y_2084_,
    );
    crate::leanh::lean_dec(v___y_2084_);
    crate::leanh::lean_dec_ref(v___y_2083_);
    crate::leanh::lean_dec(v___y_2082_);
    crate::leanh::lean_dec_ref(v___y_2081_);
    return v_res_2086_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(
    mut v___y_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWord_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leadWordIdent_2092_: u8 = 0;
    let mut v_isUngrouped_2093_: u8 = 0;
    let mut v_mustBeGrouped_2094_: u8 = 0;
    let mut v_stack_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2098_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2089_ = lean_st_ref_take(v___y_2087_);
                v_stxTrav_2090_ = crate::leanh::lean_ctor_get(v___x_2089_, 0);
                v_leadWord_2091_ = crate::leanh::lean_ctor_get(v___x_2089_, 1);
                v_leadWordIdent_2092_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2089_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isUngrouped_2093_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2089_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_mustBeGrouped_2094_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_2089_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                );
                v_stack_2095_ = crate::leanh::lean_ctor_get(v___x_2089_, 2);
                v_isSharedCheck_2106_ = (!crate::leanh::lean_is_exclusive(v___x_2089_)) as u8;
                if v_isSharedCheck_2106_ == 0 {
                    v___x_2097_ = v___x_2089_;
                    v_isShared_2098_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stack_2095_);
                    crate::leanh::lean_inc(v_leadWord_2091_);
                    crate::leanh::lean_inc(v_stxTrav_2090_);
                    crate::leanh::lean_dec(v___x_2089_);
                    v___x_2097_ = crate::leanh::lean_box(0);
                    v_isShared_2098_ = v_isSharedCheck_2106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2099_ = l_Lean_Syntax_Traverser_left(v_stxTrav_2090_);
                if v_isShared_2098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2097_, 0, v___x_2099_);
                    v___x_2101_ = v___x_2097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2105_ = crate::leanh::lean_alloc_ctor(0, 3, (3) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_leadWord_2091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_stack_2095_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2105_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_leadWordIdent_2092_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2105_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_isUngrouped_2093_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2105_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 2) as u32,
                        v_mustBeGrouped_2094_,
                    );
                    v___x_2101_ = v_reuseFailAlloc_2105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2102_ = lean_st_ref_set(v___y_2087_, v___x_2101_);
                v___x_2103_ = crate::leanh::lean_box(0);
                v___x_2104_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                return v___x_2104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg___boxed(
    mut v___y_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2109_ =
        l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(
            v___y_2107_,
        );
    crate::leanh::lean_dec(v___y_2107_);
    return v_res_2109_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(
    mut v___y_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2115_ =
        l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(
            v___y_2111_,
        );
    return v___x_2115_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___boxed(
    mut v___y_2116_: *mut crate::leanh::LeanObject,
    mut v___y_2117_: *mut crate::leanh::LeanObject,
    mut v___y_2118_: *mut crate::leanh::LeanObject,
    mut v___y_2119_: *mut crate::leanh::LeanObject,
    mut v___y_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1(
        v___y_2116_,
        v___y_2117_,
        v___y_2118_,
        v___y_2119_,
    );
    crate::leanh::lean_dec(v___y_2119_);
    crate::leanh::lean_dec_ref(v___y_2118_);
    crate::leanh::lean_dec(v___y_2117_);
    crate::leanh::lean_dec_ref(v___y_2116_);
    return v_res_2121_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2122_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2122_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2123_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__0);
    v___x_2124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2124_, 0, v___x_2123_);
    return v___x_2124_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2125_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
    v___x_2126_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2127_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2127_, 1, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2127_, 2, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2127_, 3, v___x_2126_);
    crate::leanh::lean_ctor_set(v___x_2127_, 4, v___x_2125_);
    crate::leanh::lean_ctor_set(v___x_2127_, 5, v___x_2125_);
    crate::leanh::lean_ctor_set(v___x_2127_, 6, v___x_2125_);
    crate::leanh::lean_ctor_set(v___x_2127_, 7, v___x_2125_);
    crate::leanh::lean_ctor_set(v___x_2127_, 8, v___x_2125_);
    crate::leanh::lean_ctor_set(v___x_2127_, 9, v___x_2125_);
    return v___x_2127_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2129_ = lean_mk_empty_array_with_capacity(v___x_2128_);
    v___x_2130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2130_, 0, v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: usize = 0;
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = 5usize;
    v___x_2132_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2133_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
    v___x_2135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__3);
    v___x_2136_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
    crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2134_);
    crate::leanh::lean_ctor_set(v___x_2136_, 2, v___x_2132_);
    crate::leanh::lean_ctor_set(v___x_2136_, 3, v___x_2132_);
    crate::leanh::lean_ctor_set_usize(v___x_2136_, 4, v___x_2131_);
    return v___x_2136_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = crate::leanh::lean_box(1);
    v___x_2138_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__4);
    v___x_2139_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__1);
    v___x_2140_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2140_, 0, v___x_2139_);
    crate::leanh::lean_ctor_set(v___x_2140_, 1, v___x_2138_);
    crate::leanh::lean_ctor_set(v___x_2140_, 2, v___x_2137_);
    return v___x_2140_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(
    mut v_msgData_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ = lean_st_ref_get(v___y_2143_);
    v_env_2146_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
    crate::leanh::lean_inc_ref(v_env_2146_);
    crate::leanh::lean_dec(v___x_2145_);
    v_options_2147_ = crate::leanh::lean_ctor_get(v___y_2142_, 2);
    v___x_2148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__2);
    v___x_2149_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_2147_);
    v___x_2150_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2150_, 0, v_env_2146_);
    crate::leanh::lean_ctor_set(v___x_2150_, 1, v___x_2148_);
    crate::leanh::lean_ctor_set(v___x_2150_, 2, v___x_2149_);
    crate::leanh::lean_ctor_set(v___x_2150_, 3, v_options_2147_);
    v___x_2151_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2150_);
    crate::leanh::lean_ctor_set(v___x_2151_, 1, v_msgData_2141_);
    v___x_2152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2152_, 0, v___x_2151_);
    return v___x_2152_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2___boxed(
    mut v_msgData_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msgData_2153_, v___y_2154_, v___y_2155_);
    crate::leanh::lean_dec(v___y_2155_);
    crate::leanh::lean_dec_ref(v___y_2154_);
    return v_res_2157_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: f64 = 0.0;
    v___x_2158_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2159_ = lean_float_of_nat(v___x_2158_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(
    mut v_cls_2162_: *mut crate::leanh::LeanObject,
    mut v_msg_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2185_: u8 = 0;
    let mut v_tid_2186_: u64 = 0;
    let mut v_traces_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: f64 = 0.0;
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_isSharedCheck_2213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2167_ = crate::leanh::lean_ctor_get(v___y_2164_, 5);
                v___x_2168_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2_spec__2(v_msg_2163_, v___y_2164_, v___y_2165_);
                v_a_2169_ = crate::leanh::lean_ctor_get(v___x_2168_, 0);
                v_isSharedCheck_2213_ = (!crate::leanh::lean_is_exclusive(v___x_2168_)) as u8;
                if v_isSharedCheck_2213_ == 0 {
                    v___x_2171_ = v___x_2168_;
                    v_isShared_2172_ = v_isSharedCheck_2213_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2169_);
                    crate::leanh::lean_dec(v___x_2168_);
                    v___x_2171_ = crate::leanh::lean_box(0);
                    v_isShared_2172_ = v_isSharedCheck_2213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2173_ = lean_st_ref_take(v___y_2165_);
                v_traceState_2174_ = crate::leanh::lean_ctor_get(v___x_2173_, 4);
                v_env_2175_ = crate::leanh::lean_ctor_get(v___x_2173_, 0);
                v_nextMacroScope_2176_ = crate::leanh::lean_ctor_get(v___x_2173_, 1);
                v_ngen_2177_ = crate::leanh::lean_ctor_get(v___x_2173_, 2);
                v_auxDeclNGen_2178_ = crate::leanh::lean_ctor_get(v___x_2173_, 3);
                v_cache_2179_ = crate::leanh::lean_ctor_get(v___x_2173_, 5);
                v_messages_2180_ = crate::leanh::lean_ctor_get(v___x_2173_, 6);
                v_infoState_2181_ = crate::leanh::lean_ctor_get(v___x_2173_, 7);
                v_snapshotTasks_2182_ = crate::leanh::lean_ctor_get(v___x_2173_, 8);
                v_isSharedCheck_2212_ = (!crate::leanh::lean_is_exclusive(v___x_2173_)) as u8;
                if v_isSharedCheck_2212_ == 0 {
                    v___x_2184_ = v___x_2173_;
                    v_isShared_2185_ = v_isSharedCheck_2212_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2182_);
                    crate::leanh::lean_inc(v_infoState_2181_);
                    crate::leanh::lean_inc(v_messages_2180_);
                    crate::leanh::lean_inc(v_cache_2179_);
                    crate::leanh::lean_inc(v_traceState_2174_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2178_);
                    crate::leanh::lean_inc(v_ngen_2177_);
                    crate::leanh::lean_inc(v_nextMacroScope_2176_);
                    crate::leanh::lean_inc(v_env_2175_);
                    crate::leanh::lean_dec(v___x_2173_);
                    v___x_2184_ = crate::leanh::lean_box(0);
                    v_isShared_2185_ = v_isSharedCheck_2212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2186_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2174_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2187_ = crate::leanh::lean_ctor_get(v_traceState_2174_, 0);
                v_isSharedCheck_2211_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2174_)) as u8;
                if v_isSharedCheck_2211_ == 0 {
                    v___x_2189_ = v_traceState_2174_;
                    v_isShared_2190_ = v_isSharedCheck_2211_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2187_);
                    crate::leanh::lean_dec(v_traceState_2174_);
                    v___x_2189_ = crate::leanh::lean_box(0);
                    v_isShared_2190_ = v_isSharedCheck_2211_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2191_ = crate::leanh::lean_box(0);
                v___x_2192_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__0);
                v___x_2193_ = 0;
                v___x_2194_ = l_Lake_Toml_mkUnexpectedCharError___closed__1;
                v___x_2195_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2195_, 0, v_cls_2162_);
                crate::leanh::lean_ctor_set(v___x_2195_, 1, v___x_2191_);
                crate::leanh::lean_ctor_set(v___x_2195_, 2, v___x_2194_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2195_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2192_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2195_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2192_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2195_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2193_,
                );
                v___x_2196_ =
                    l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___closed__1;
                v___x_2197_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2197_, 0, v___x_2195_);
                crate::leanh::lean_ctor_set(v___x_2197_, 1, v_a_2169_);
                crate::leanh::lean_ctor_set(v___x_2197_, 2, v___x_2196_);
                crate::leanh::lean_inc(v_ref_2167_);
                v___x_2198_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2198_, 0, v_ref_2167_);
                crate::leanh::lean_ctor_set(v___x_2198_, 1, v___x_2197_);
                v___x_2199_ = l_Lean_PersistentArray_push___redArg(v_traces_2187_, v___x_2198_);
                if v_isShared_2190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2199_);
                    v___x_2201_ = v___x_2189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2210_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2199_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2210_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2186_,
                    );
                    v___x_2201_ = v_reuseFailAlloc_2210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2184_, 4, v___x_2201_);
                    v___x_2203_ = v___x_2184_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_env_2175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_nextMacroScope_2176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_ngen_2177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_auxDeclNGen_2178_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 5, v_cache_2179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 6, v_messages_2180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 7, v_infoState_2181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 8, v_snapshotTasks_2182_);
                    v___x_2203_ = v_reuseFailAlloc_2209_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2204_ = lean_st_ref_set(v___y_2165_, v___x_2203_);
                v___x_2205_ = crate::leanh::lean_box(0);
                if v_isShared_2172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2205_);
                    v___x_2207_ = v___x_2171_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg___boxed(
    mut v_cls_2214_: *mut crate::leanh::LeanObject,
    mut v_msg_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2219_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(
        v_cls_2214_,
        v_msg_2215_,
        v___y_2216_,
        v___y_2217_,
    );
    crate::leanh::lean_dec(v___y_2217_);
    crate::leanh::lean_dec_ref(v___y_2216_);
    return v_res_2219_;
}
pub unsafe fn _init_l_Lake_Toml_atom_formatter___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lake_Toml_atom_formatter___redArg___closed__3;
    v___x_2231_ = l_Lake_Toml_atom_formatter___redArg___closed__5;
    v___x_2232_ = l_Lean_Name_append(v___x_2231_, v___x_2230_);
    return v___x_2232_;
}
pub unsafe fn _init_l_Lake_Toml_atom_formatter___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2234_ = l_Lake_Toml_atom_formatter___redArg___closed__7;
    v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
    return v___x_2235_;
}
pub unsafe fn _init_l_Lake_Toml_atom_formatter___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Lake_Toml_atom_formatter___redArg___closed__9;
    v___x_2238_ = l_Lean_stringToMessageData(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lake_Toml_atom_formatter___redArg(
    mut v_a_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(
            v_a_2240_,
        );
    v_a_2245_ = crate::leanh::lean_ctor_get(v___x_2244_, 0);
    crate::leanh::lean_inc(v_a_2245_);
    crate::leanh::lean_dec_ref(v___x_2244_);
    if crate::leanh::lean_obj_tag(v_a_2245_) == 2 {
        let mut v_info_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_val_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2249_: u8 = 0;
        let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_info_2246_ = crate::leanh::lean_ctor_get(v_a_2245_, 0);
        crate::leanh::lean_inc(v_info_2246_);
        v_val_2247_ = crate::leanh::lean_ctor_get(v_a_2245_, 1);
        crate::leanh::lean_inc_ref(v_val_2247_);
        v___x_2248_ = l_Lean_PrettyPrinter_Formatter_getExprPos_x3f(v_a_2245_);
        crate::leanh::lean_dec_ref_known(v_a_2245_, 2);
        v___x_2249_ = 0;
        v___x_2250_ = crate::leanh::lean_box((v___x_2249_) as usize);
        v___x_2251_ = crate::leanh::lean_alloc_closure(
            l_Lean_PrettyPrinter_Formatter_pushToken___boxed as *mut core::ffi::c_void,
            8,
            3,
        );
        crate::leanh::lean_closure_set(v___x_2251_, 0, v_info_2246_);
        crate::leanh::lean_closure_set(v___x_2251_, 1, v_val_2247_);
        crate::leanh::lean_closure_set(v___x_2251_, 2, v___x_2250_);
        v___x_2252_ = l_Lean_PrettyPrinter_Formatter_withMaybeTag(
            v___x_2248_,
            v___x_2251_,
            v_a_2239_,
            v_a_2240_,
            v_a_2241_,
            v_a_2242_,
        );
        crate::leanh::lean_dec(v___x_2248_);
        if crate::leanh::lean_obj_tag(v___x_2252_) == 0 {
            let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2252_, 1);
            v___x_2253_ = l_Lean_Syntax_MonadTraverser_goLeft___at___00Lake_Toml_atom_formatter_spec__1___redArg(v_a_2240_);
            return v___x_2253_;
        } else {
            return v___x_2252_;
        }
    } else {
        let mut v_options_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_hasTrace_2255_: u8 = 0;
        v_options_2254_ = crate::leanh::lean_ctor_get(v_a_2241_, 2);
        v_hasTrace_2255_ = crate::leanh::lean_ctor_get_uint8(
            v_options_2254_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        if v_hasTrace_2255_ == 0 {
            let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_2245_);
            v___x_2256_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
            return v___x_2256_;
        } else {
            let mut v_inheritedTraceOptions_2257_: *mut crate::leanh::LeanObject =
                core::ptr::null_mut();
            let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2260_: u8 = 0;
            v_inheritedTraceOptions_2257_ = crate::leanh::lean_ctor_get(v_a_2241_, 13);
            v___x_2258_ = l_Lake_Toml_atom_formatter___redArg___closed__3;
            v___x_2259_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__6),
                core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__6_once),
                _init_l_Lake_Toml_atom_formatter___redArg___closed__6,
            );
            v___x_2260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                v_inheritedTraceOptions_2257_,
                v_options_2254_,
                v___x_2259_,
            );
            if v___x_2260_ == 0 {
                let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_a_2245_);
                v___x_2261_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
                return v___x_2261_;
            } else {
                let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2264_: u8 = 0;
                let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2262_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__8),
                    core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__8_once),
                    _init_l_Lake_Toml_atom_formatter___redArg___closed__8,
                );
                v___x_2263_ = crate::leanh::lean_box(0);
                v___x_2264_ = 0;
                v___x_2265_ = l_Lean_Syntax_formatStx(v_a_2245_, v___x_2263_, v___x_2264_);
                v___x_2266_ = l_Lean_MessageData_ofFormat(v___x_2265_);
                v___x_2267_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2262_);
                crate::leanh::lean_ctor_set(v___x_2267_, 1, v___x_2266_);
                v___x_2268_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__10),
                    core::ptr::addr_of_mut!(l_Lake_Toml_atom_formatter___redArg___closed__10_once),
                    _init_l_Lake_Toml_atom_formatter___redArg___closed__10,
                );
                v___x_2269_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2269_, 0, v___x_2267_);
                crate::leanh::lean_ctor_set(v___x_2269_, 1, v___x_2268_);
                v___x_2270_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(
                    v___x_2258_,
                    v___x_2269_,
                    v_a_2241_,
                    v_a_2242_,
                );
                if crate::leanh::lean_obj_tag(v___x_2270_) == 0 {
                    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v___x_2270_, 1);
                    v___x_2271_ = l_Lean_PrettyPrinter_Formatter_throwBacktrack___redArg();
                    return v___x_2271_;
                } else {
                    return v___x_2270_;
                }
            }
        }
    }
}
pub unsafe fn l_Lake_Toml_atom_formatter___redArg___boxed(
    mut v_a_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v_a_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lake_Toml_atom_formatter___redArg(v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
    crate::leanh::lean_dec(v_a_2275_);
    crate::leanh::lean_dec_ref(v_a_2274_);
    crate::leanh::lean_dec(v_a_2273_);
    crate::leanh::lean_dec_ref(v_a_2272_);
    return v_res_2277_;
}
pub unsafe fn l_Lake_Toml_atom_formatter(
    mut v_x_2278_: *mut crate::leanh::LeanObject,
    mut v_x_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2285_ = l_Lake_Toml_atom_formatter___redArg(v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
    return v___x_2285_;
}
pub unsafe fn l_Lake_Toml_atom_formatter___boxed(
    mut v_x_2286_: *mut crate::leanh::LeanObject,
    mut v_x_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_a_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2293_ = l_Lake_Toml_atom_formatter(
        v_x_2286_, v_x_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_,
    );
    crate::leanh::lean_dec(v_a_2291_);
    crate::leanh::lean_dec_ref(v_a_2290_);
    crate::leanh::lean_dec(v_a_2289_);
    crate::leanh::lean_dec_ref(v_a_2288_);
    crate::leanh::lean_dec_ref(v_x_2287_);
    crate::leanh::lean_dec_ref(v_x_2286_);
    return v_res_2293_;
}
pub unsafe fn l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(
    mut v_cls_2294_: *mut crate::leanh::LeanObject,
    mut v_msg_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2301_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___redArg(
        v_cls_2294_,
        v_msg_2295_,
        v___y_2298_,
        v___y_2299_,
    );
    return v___x_2301_;
}
pub unsafe fn l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2___boxed(
    mut v_cls_2302_: *mut crate::leanh::LeanObject,
    mut v_msg_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Lean_addTrace___at___00Lake_Toml_atom_formatter_spec__2(
        v_cls_2302_,
        v_msg_2303_,
        v___y_2304_,
        v___y_2305_,
        v___y_2306_,
        v___y_2307_,
    );
    crate::leanh::lean_dec(v___y_2307_);
    crate::leanh::lean_dec_ref(v___y_2306_);
    crate::leanh::lean_dec(v___y_2305_);
    crate::leanh::lean_dec_ref(v___y_2304_);
    return v_res_2309_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(
    mut v_a_2310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2310_);
    return v___x_2312_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg___boxed(
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_a_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2315_ =
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___redArg(v_a_2313_);
    crate::leanh::lean_dec(v_a_2313_);
    return v_res_2315_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(
    mut v_x_2316_: *mut crate::leanh::LeanObject,
    mut v_x_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2323_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2319_);
    return v___x_2323_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer___boxed(
    mut v_x_2324_: *mut crate::leanh::LeanObject,
    mut v_x_2325_: *mut crate::leanh::LeanObject,
    mut v_a_2326_: *mut crate::leanh::LeanObject,
    mut v_a_2327_: *mut crate::leanh::LeanObject,
    mut v_a_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_atom_parenthesizer(
        v_x_2324_, v_x_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_,
    );
    crate::leanh::lean_dec(v_a_2329_);
    crate::leanh::lean_dec_ref(v_a_2328_);
    crate::leanh::lean_dec(v_a_2327_);
    crate::leanh::lean_dec_ref(v_a_2326_);
    crate::leanh::lean_dec_ref(v_x_2325_);
    crate::leanh::lean_dec_ref(v_x_2324_);
    return v_res_2331_;
}
pub unsafe fn l_Lake_Toml_chAtom(
    mut v_c_2332_: u32,
    mut v_expected_2333_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = crate::leanh::lean_box_uint32(v_c_2332_);
    v___x_2336_ =
        crate::leanh::lean_alloc_closure(l_Lake_Toml_chFn___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2336_, 0, v___x_2335_);
    crate::leanh::lean_closure_set(v___x_2336_, 1, v_expected_2333_);
    v___x_2337_ = l_Lake_Toml_atom(v___x_2336_, v_trailingFn_2334_);
    return v___x_2337_;
}
pub unsafe fn l_Lake_Toml_chAtom___boxed(
    mut v_c_2338_: *mut crate::leanh::LeanObject,
    mut v_expected_2339_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2341_: u32 = 0;
    let mut v_res_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2341_ = crate::leanh::lean_unbox_uint32(v_c_2338_);
    crate::leanh::lean_dec(v_c_2338_);
    v_res_2342_ = l_Lake_Toml_chAtom(v_c_boxed_2341_, v_expected_2339_, v_trailingFn_2340_);
    return v_res_2342_;
}
pub unsafe fn l_Lake_Toml_chAtom_formatter___redArg(
    mut v_c_2343_: u32,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2349_ = 0;
    v___x_2350_ = l_Lean_PrettyPrinter_Formatter_rawCh_formatter(
        v_c_2343_,
        v___x_2349_,
        v_a_2344_,
        v_a_2345_,
        v_a_2346_,
        v_a_2347_,
    );
    return v___x_2350_;
}
pub unsafe fn l_Lake_Toml_chAtom_formatter___redArg___boxed(
    mut v_c_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
    mut v_a_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2357_: u32 = 0;
    let mut v_res_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2357_ = crate::leanh::lean_unbox_uint32(v_c_2351_);
    crate::leanh::lean_dec(v_c_2351_);
    v_res_2358_ = l_Lake_Toml_chAtom_formatter___redArg(
        v_c_boxed_2357_,
        v_a_2352_,
        v_a_2353_,
        v_a_2354_,
        v_a_2355_,
    );
    crate::leanh::lean_dec(v_a_2355_);
    crate::leanh::lean_dec_ref(v_a_2354_);
    crate::leanh::lean_dec(v_a_2353_);
    crate::leanh::lean_dec_ref(v_a_2352_);
    return v_res_2358_;
}
pub unsafe fn l_Lake_Toml_chAtom_formatter(
    mut v_c_2359_: u32,
    mut v_x_2360_: *mut crate::leanh::LeanObject,
    mut v_x_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = l_Lake_Toml_chAtom_formatter___redArg(
        v_c_2359_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_,
    );
    return v___x_2367_;
}
pub unsafe fn l_Lake_Toml_chAtom_formatter___boxed(
    mut v_c_2368_: *mut crate::leanh::LeanObject,
    mut v_x_2369_: *mut crate::leanh::LeanObject,
    mut v_x_2370_: *mut crate::leanh::LeanObject,
    mut v_a_2371_: *mut crate::leanh::LeanObject,
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2376_: u32 = 0;
    let mut v_res_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2376_ = crate::leanh::lean_unbox_uint32(v_c_2368_);
    crate::leanh::lean_dec(v_c_2368_);
    v_res_2377_ = l_Lake_Toml_chAtom_formatter(
        v_c_boxed_2376_,
        v_x_2369_,
        v_x_2370_,
        v_a_2371_,
        v_a_2372_,
        v_a_2373_,
        v_a_2374_,
    );
    crate::leanh::lean_dec(v_a_2374_);
    crate::leanh::lean_dec_ref(v_a_2373_);
    crate::leanh::lean_dec(v_a_2372_);
    crate::leanh::lean_dec_ref(v_a_2371_);
    crate::leanh::lean_dec_ref(v_x_2370_);
    crate::leanh::lean_dec(v_x_2369_);
    return v_res_2377_;
}
pub unsafe fn l_Lake_Toml_chAtom_parenthesizer___redArg(
    mut v_a_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2380_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2378_);
    return v___x_2380_;
}
pub unsafe fn l_Lake_Toml_chAtom_parenthesizer___redArg___boxed(
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Lake_Toml_chAtom_parenthesizer___redArg(v_a_2381_);
    crate::leanh::lean_dec(v_a_2381_);
    return v_res_2383_;
}
pub unsafe fn l_Lake_Toml_chAtom_parenthesizer(
    mut v_x_2384_: u32,
    mut v_x_2385_: *mut crate::leanh::LeanObject,
    mut v_x_2386_: *mut crate::leanh::LeanObject,
    mut v_a_2387_: *mut crate::leanh::LeanObject,
    mut v_a_2388_: *mut crate::leanh::LeanObject,
    mut v_a_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2388_);
    return v___x_2392_;
}
pub unsafe fn l_Lake_Toml_chAtom_parenthesizer___boxed(
    mut v_x_2393_: *mut crate::leanh::LeanObject,
    mut v_x_2394_: *mut crate::leanh::LeanObject,
    mut v_x_2395_: *mut crate::leanh::LeanObject,
    mut v_a_2396_: *mut crate::leanh::LeanObject,
    mut v_a_2397_: *mut crate::leanh::LeanObject,
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_a_2399_: *mut crate::leanh::LeanObject,
    mut v_a_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18__boxed_2401_: u32 = 0;
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_2401_ = crate::leanh::lean_unbox_uint32(v_x_2393_);
    crate::leanh::lean_dec(v_x_2393_);
    v_res_2402_ = l_Lake_Toml_chAtom_parenthesizer(
        v_x_18__boxed_2401_,
        v_x_2394_,
        v_x_2395_,
        v_a_2396_,
        v_a_2397_,
        v_a_2398_,
        v_a_2399_,
    );
    crate::leanh::lean_dec(v_a_2399_);
    crate::leanh::lean_dec_ref(v_a_2398_);
    crate::leanh::lean_dec(v_a_2397_);
    crate::leanh::lean_dec_ref(v_a_2396_);
    crate::leanh::lean_dec_ref(v_x_2395_);
    crate::leanh::lean_dec(v_x_2394_);
    return v_res_2402_;
}
pub unsafe fn l_Lake_Toml_strAtom(
    mut v_s_2403_: *mut crate::leanh::LeanObject,
    mut v_expected_2404_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2407_ = lean_string_utf8_byte_size(v_s_2403_);
    v___x_2408_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2408_, 0, v_s_2403_);
    crate::leanh::lean_ctor_set(v___x_2408_, 1, v___x_2406_);
    crate::leanh::lean_ctor_set(v___x_2408_, 2, v___x_2407_);
    v___x_2409_ = l_String_Slice_trimAscii(v___x_2408_);
    v_str_2410_ = crate::leanh::lean_ctor_get(v___x_2409_, 0);
    crate::leanh::lean_inc_ref(v_str_2410_);
    v_startInclusive_2411_ = crate::leanh::lean_ctor_get(v___x_2409_, 1);
    crate::leanh::lean_inc(v_startInclusive_2411_);
    v_endExclusive_2412_ = crate::leanh::lean_ctor_get(v___x_2409_, 2);
    crate::leanh::lean_inc(v_endExclusive_2412_);
    crate::leanh::lean_dec_ref(v___x_2409_);
    v___x_2413_ =
        lean_string_utf8_extract(v_str_2410_, v_startInclusive_2411_, v_endExclusive_2412_);
    crate::leanh::lean_dec(v_endExclusive_2412_);
    crate::leanh::lean_dec(v_startInclusive_2411_);
    crate::leanh::lean_dec_ref(v_str_2410_);
    v___x_2414_ =
        crate::leanh::lean_alloc_closure(l_Lake_Toml_strFn as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2414_, 0, v___x_2413_);
    crate::leanh::lean_closure_set(v___x_2414_, 1, v_expected_2404_);
    v___x_2415_ = l_Lake_Toml_atom(v___x_2414_, v_trailingFn_2405_);
    return v___x_2415_;
}
pub unsafe fn l_Lake_Toml_strAtom_formatter___redArg(
    mut v_s_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(
        v_s_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_,
    );
    return v___x_2422_;
}
pub unsafe fn l_Lake_Toml_strAtom_formatter___redArg___boxed(
    mut v_s_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
    mut v_a_2425_: *mut crate::leanh::LeanObject,
    mut v_a_2426_: *mut crate::leanh::LeanObject,
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_a_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2429_ = l_Lake_Toml_strAtom_formatter___redArg(
        v_s_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_,
    );
    crate::leanh::lean_dec(v_a_2427_);
    crate::leanh::lean_dec_ref(v_a_2426_);
    crate::leanh::lean_dec(v_a_2425_);
    crate::leanh::lean_dec_ref(v_a_2424_);
    return v_res_2429_;
}
pub unsafe fn l_Lake_Toml_strAtom_formatter(
    mut v_s_2430_: *mut crate::leanh::LeanObject,
    mut v_x_2431_: *mut crate::leanh::LeanObject,
    mut v_x_2432_: *mut crate::leanh::LeanObject,
    mut v_a_2433_: *mut crate::leanh::LeanObject,
    mut v_a_2434_: *mut crate::leanh::LeanObject,
    mut v_a_2435_: *mut crate::leanh::LeanObject,
    mut v_a_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = l_Lean_PrettyPrinter_Formatter_symbolNoAntiquot_formatter(
        v_s_2430_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_,
    );
    return v___x_2438_;
}
pub unsafe fn l_Lake_Toml_strAtom_formatter___boxed(
    mut v_s_2439_: *mut crate::leanh::LeanObject,
    mut v_x_2440_: *mut crate::leanh::LeanObject,
    mut v_x_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2447_ = l_Lake_Toml_strAtom_formatter(
        v_s_2439_, v_x_2440_, v_x_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_,
    );
    crate::leanh::lean_dec(v_a_2445_);
    crate::leanh::lean_dec_ref(v_a_2444_);
    crate::leanh::lean_dec(v_a_2443_);
    crate::leanh::lean_dec_ref(v_a_2442_);
    crate::leanh::lean_dec_ref(v_x_2441_);
    crate::leanh::lean_dec(v_x_2440_);
    return v_res_2447_;
}
pub unsafe fn l_Lake_Toml_strAtom_parenthesizer___redArg(
    mut v_a_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2448_);
    return v___x_2450_;
}
pub unsafe fn l_Lake_Toml_strAtom_parenthesizer___redArg___boxed(
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lake_Toml_strAtom_parenthesizer___redArg(v_a_2451_);
    crate::leanh::lean_dec(v_a_2451_);
    return v_res_2453_;
}
pub unsafe fn l_Lake_Toml_strAtom_parenthesizer(
    mut v_x_2454_: *mut crate::leanh::LeanObject,
    mut v_x_2455_: *mut crate::leanh::LeanObject,
    mut v_x_2456_: *mut crate::leanh::LeanObject,
    mut v_a_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2458_);
    return v___x_2462_;
}
pub unsafe fn l_Lake_Toml_strAtom_parenthesizer___boxed(
    mut v_x_2463_: *mut crate::leanh::LeanObject,
    mut v_x_2464_: *mut crate::leanh::LeanObject,
    mut v_x_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2471_ = l_Lake_Toml_strAtom_parenthesizer(
        v_x_2463_, v_x_2464_, v_x_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_,
    );
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec_ref(v_a_2468_);
    crate::leanh::lean_dec(v_a_2467_);
    crate::leanh::lean_dec_ref(v_a_2466_);
    crate::leanh::lean_dec_ref(v_x_2465_);
    crate::leanh::lean_dec(v_x_2464_);
    crate::leanh::lean_dec_ref(v_x_2463_);
    return v_res_2471_;
}
pub unsafe fn l_Lake_Toml_pushLit(
    mut v_kind_2472_: *mut crate::leanh::LeanObject,
    mut v_startPos_2473_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2474_: *mut crate::leanh::LeanObject,
    mut v_c_2475_: *mut crate::leanh::LeanObject,
    mut v_s_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toInputContext_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inputString_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v_leading_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: u8 = 0;
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2498_: u8 = 0;
    let mut v_unused_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toInputContext_2477_ = crate::leanh::lean_ctor_get(v_c_2475_, 0);
                crate::leanh::lean_inc_ref(v_toInputContext_2477_);
                v_pos_2478_ = crate::leanh::lean_ctor_get(v_s_2476_, 2);
                crate::leanh::lean_inc(v_pos_2478_);
                v_inputString_2479_ = crate::leanh::lean_ctor_get(v_toInputContext_2477_, 0);
                v_endPos_2480_ = crate::leanh::lean_ctor_get(v_toInputContext_2477_, 3);
                v_isSharedCheck_2498_ =
                    (!crate::leanh::lean_is_exclusive(v_toInputContext_2477_)) as u8;
                if v_isSharedCheck_2498_ == 0 {
                    v_unused_2499_ = crate::leanh::lean_ctor_get(v_toInputContext_2477_, 2);
                    crate::leanh::lean_dec(v_unused_2499_);
                    v_unused_2500_ = crate::leanh::lean_ctor_get(v_toInputContext_2477_, 1);
                    crate::leanh::lean_dec(v_unused_2500_);
                    v___x_2482_ = v_toInputContext_2477_;
                    v_isShared_2483_ = v_isSharedCheck_2498_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endPos_2480_);
                    crate::leanh::lean_inc(v_inputString_2479_);
                    crate::leanh::lean_dec(v_toInputContext_2477_);
                    v___x_2482_ = crate::leanh::lean_box(0);
                    v_isShared_2483_ = v_isSharedCheck_2498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_startPos_2473_);
                v_leading_2484_ =
                    l_Lean_Parser_ParserContext_mkEmptySubstringAt(v_c_2475_, v_startPos_2473_);
                v_s_2485_ = crate::leanh::lean_apply_2(v_trailingFn_2474_, v_c_2475_, v_s_2476_);
                v_pos_2486_ = crate::leanh::lean_ctor_get(v_s_2485_, 2);
                crate::leanh::lean_inc(v_pos_2486_);
                v_val_2487_ =
                    lean_string_utf8_extract(v_inputString_2479_, v_startPos_2473_, v_pos_2478_);
                v___x_2495_ = lean_nat_dec_le(v_pos_2486_, v_endPos_2480_);
                if v___x_2495_ == 0 {
                    crate::leanh::lean_dec(v_pos_2486_);
                    crate::leanh::lean_inc(v_pos_2478_);
                    v___x_2496_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2496_, 0, v_inputString_2479_);
                    crate::leanh::lean_ctor_set(v___x_2496_, 1, v_pos_2478_);
                    crate::leanh::lean_ctor_set(v___x_2496_, 2, v_endPos_2480_);
                    v___y_2489_ = v___x_2496_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_endPos_2480_);
                    crate::leanh::lean_inc(v_pos_2478_);
                    v___x_2497_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2497_, 0, v_inputString_2479_);
                    crate::leanh::lean_ctor_set(v___x_2497_, 1, v_pos_2478_);
                    crate::leanh::lean_ctor_set(v___x_2497_, 2, v_pos_2486_);
                    v___y_2489_ = v___x_2497_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2482_, 3, v_pos_2478_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 2, v___y_2489_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 1, v_startPos_2473_);
                    crate::leanh::lean_ctor_set(v___x_2482_, 0, v_leading_2484_);
                    v_info_2491_ = v___x_2482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_leading_2484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_startPos_2473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 2, v___y_2489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_pos_2478_);
                    v_info_2491_ = v_reuseFailAlloc_2494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2492_ = l_Lean_Syntax_mkLit(v_kind_2472_, v_val_2487_, v_info_2491_);
                v___x_2493_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2485_, v___x_2492_);
                return v___x_2493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_litFn(
    mut v_kind_2501_: *mut crate::leanh::LeanObject,
    mut v_p_2502_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2503_: *mut crate::leanh::LeanObject,
    mut v_c_2504_: *mut crate::leanh::LeanObject,
    mut v_s_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_errorMsg_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    v_pos_2506_ = crate::leanh::lean_ctor_get(v_s_2505_, 2);
    crate::leanh::lean_inc(v_pos_2506_);
    crate::leanh::lean_inc_ref(v_c_2504_);
    v_s_2507_ = crate::leanh::lean_apply_2(v_p_2502_, v_c_2504_, v_s_2505_);
    v_errorMsg_2508_ = crate::leanh::lean_ctor_get(v_s_2507_, 4);
    crate::leanh::lean_inc(v_errorMsg_2508_);
    v___x_2509_ = crate::leanh::lean_box(0);
    v___x_2510_ =
        l_Option_instBEq_beq___at___00Lake_Toml_optFn_spec__0(v_errorMsg_2508_, v___x_2509_);
    if v___x_2510_ == 0 {
        crate::leanh::lean_dec(v_pos_2506_);
        crate::leanh::lean_dec_ref(v_c_2504_);
        crate::leanh::lean_dec_ref(v_trailingFn_2503_);
        crate::leanh::lean_dec(v_kind_2501_);
        return v_s_2507_;
    } else {
        let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2511_ = l_Lake_Toml_pushLit(
            v_kind_2501_,
            v_pos_2506_,
            v_trailingFn_2503_,
            v_c_2504_,
            v_s_2507_,
        );
        return v___x_2511_;
    }
}
pub unsafe fn l_Lake_Toml_lit(
    mut v_kind_2512_: *mut crate::leanh::LeanObject,
    mut v_p_2513_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lake_Toml_atom___closed__2;
    v___x_2516_ =
        crate::leanh::lean_alloc_closure(l_Lake_Toml_litFn as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2516_, 0, v_kind_2512_);
    crate::leanh::lean_closure_set(v___x_2516_, 1, v_p_2513_);
    crate::leanh::lean_closure_set(v___x_2516_, 2, v_trailingFn_2514_);
    v___x_2517_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2515_);
    crate::leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
    return v___x_2517_;
}
pub unsafe fn l_Lake_Toml_lit_formatter___redArg(
    mut v_kind_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
        v_kind_2518_,
        v_a_2519_,
        v_a_2520_,
        v_a_2521_,
        v_a_2522_,
    );
    return v___x_2524_;
}
pub unsafe fn l_Lake_Toml_lit_formatter___redArg___boxed(
    mut v_kind_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v_a_2529_: *mut crate::leanh::LeanObject,
    mut v_a_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2531_ = l_Lake_Toml_lit_formatter___redArg(
        v_kind_2525_,
        v_a_2526_,
        v_a_2527_,
        v_a_2528_,
        v_a_2529_,
    );
    crate::leanh::lean_dec(v_a_2529_);
    crate::leanh::lean_dec_ref(v_a_2528_);
    crate::leanh::lean_dec(v_a_2527_);
    crate::leanh::lean_dec_ref(v_a_2526_);
    return v_res_2531_;
}
pub unsafe fn l_Lake_Toml_lit_formatter(
    mut v_kind_2532_: *mut crate::leanh::LeanObject,
    mut v_x_2533_: *mut crate::leanh::LeanObject,
    mut v_x_2534_: *mut crate::leanh::LeanObject,
    mut v_a_2535_: *mut crate::leanh::LeanObject,
    mut v_a_2536_: *mut crate::leanh::LeanObject,
    mut v_a_2537_: *mut crate::leanh::LeanObject,
    mut v_a_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
        v_kind_2532_,
        v_a_2535_,
        v_a_2536_,
        v_a_2537_,
        v_a_2538_,
    );
    return v___x_2540_;
}
pub unsafe fn l_Lake_Toml_lit_formatter___boxed(
    mut v_kind_2541_: *mut crate::leanh::LeanObject,
    mut v_x_2542_: *mut crate::leanh::LeanObject,
    mut v_x_2543_: *mut crate::leanh::LeanObject,
    mut v_a_2544_: *mut crate::leanh::LeanObject,
    mut v_a_2545_: *mut crate::leanh::LeanObject,
    mut v_a_2546_: *mut crate::leanh::LeanObject,
    mut v_a_2547_: *mut crate::leanh::LeanObject,
    mut v_a_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2549_ = l_Lake_Toml_lit_formatter(
        v_kind_2541_,
        v_x_2542_,
        v_x_2543_,
        v_a_2544_,
        v_a_2545_,
        v_a_2546_,
        v_a_2547_,
    );
    crate::leanh::lean_dec(v_a_2547_);
    crate::leanh::lean_dec_ref(v_a_2546_);
    crate::leanh::lean_dec(v_a_2545_);
    crate::leanh::lean_dec_ref(v_a_2544_);
    crate::leanh::lean_dec_ref(v_x_2543_);
    crate::leanh::lean_dec_ref(v_x_2542_);
    return v_res_2549_;
}
pub unsafe fn l_Lake_Toml_lit_parenthesizer___redArg(
    mut v_a_2550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2550_);
    return v___x_2552_;
}
pub unsafe fn l_Lake_Toml_lit_parenthesizer___redArg___boxed(
    mut v_a_2553_: *mut crate::leanh::LeanObject,
    mut v_a_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2555_ = l_Lake_Toml_lit_parenthesizer___redArg(v_a_2553_);
    crate::leanh::lean_dec(v_a_2553_);
    return v_res_2555_;
}
pub unsafe fn l_Lake_Toml_lit_parenthesizer(
    mut v_x_2556_: *mut crate::leanh::LeanObject,
    mut v_x_2557_: *mut crate::leanh::LeanObject,
    mut v_x_2558_: *mut crate::leanh::LeanObject,
    mut v_a_2559_: *mut crate::leanh::LeanObject,
    mut v_a_2560_: *mut crate::leanh::LeanObject,
    mut v_a_2561_: *mut crate::leanh::LeanObject,
    mut v_a_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v_a_2560_);
    return v___x_2564_;
}
pub unsafe fn l_Lake_Toml_lit_parenthesizer___boxed(
    mut v_x_2565_: *mut crate::leanh::LeanObject,
    mut v_x_2566_: *mut crate::leanh::LeanObject,
    mut v_x_2567_: *mut crate::leanh::LeanObject,
    mut v_a_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
    mut v_a_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2573_ = l_Lake_Toml_lit_parenthesizer(
        v_x_2565_, v_x_2566_, v_x_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_,
    );
    crate::leanh::lean_dec(v_a_2571_);
    crate::leanh::lean_dec_ref(v_a_2570_);
    crate::leanh::lean_dec(v_a_2569_);
    crate::leanh::lean_dec_ref(v_a_2568_);
    crate::leanh::lean_dec_ref(v_x_2567_);
    crate::leanh::lean_dec_ref(v_x_2566_);
    crate::leanh::lean_dec(v_x_2565_);
    return v_res_2573_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(
    mut v_kind_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2580_ = l_Lean_PrettyPrinter_Formatter_visitAtom(
        v_kind_2574_,
        v___y_2575_,
        v___y_2576_,
        v___y_2577_,
        v___y_2578_,
    );
    return v___x_2580_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed(
    mut v_kind_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2587_ = l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0(
        v_kind_2581_,
        v___y_2582_,
        v___y_2583_,
        v___y_2584_,
        v___y_2585_,
    );
    crate::leanh::lean_dec(v___y_2585_);
    crate::leanh::lean_dec_ref(v___y_2584_);
    crate::leanh::lean_dec(v___y_2583_);
    crate::leanh::lean_dec_ref(v___y_2582_);
    return v_res_2587_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter___redArg(
    mut v_name_2588_: *mut crate::leanh::LeanObject,
    mut v_kind_2589_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2590_: u8,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_kind_2589_);
    v___f_2596_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_litWithAntiquot_formatter___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2596_, 0, v_kind_2589_);
    v___x_2597_ = 0;
    v___x_2598_ = crate::leanh::lean_box((v_anonymous_2590_) as usize);
    v___x_2599_ = crate::leanh::lean_box((v___x_2597_) as usize);
    v___x_2600_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_formatter___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_2600_, 0, v_name_2588_);
    crate::leanh::lean_closure_set(v___x_2600_, 1, v_kind_2589_);
    crate::leanh::lean_closure_set(v___x_2600_, 2, v___x_2598_);
    crate::leanh::lean_closure_set(v___x_2600_, 3, v___x_2599_);
    v___x_2601_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_2600_,
        v___f_2596_,
        v_a_2591_,
        v_a_2592_,
        v_a_2593_,
        v_a_2594_,
    );
    return v___x_2601_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter___redArg___boxed(
    mut v_name_2602_: *mut crate::leanh::LeanObject,
    mut v_kind_2603_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2610_: u8 = 0;
    let mut v_res_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2610_ = (crate::leanh::lean_unbox(v_anonymous_2604_) as u8);
    v_res_2611_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v_name_2602_,
        v_kind_2603_,
        v_anonymous_boxed_2610_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
        v_a_2608_,
    );
    crate::leanh::lean_dec(v_a_2608_);
    crate::leanh::lean_dec_ref(v_a_2607_);
    crate::leanh::lean_dec(v_a_2606_);
    crate::leanh::lean_dec_ref(v_a_2605_);
    return v_res_2611_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter(
    mut v_name_2612_: *mut crate::leanh::LeanObject,
    mut v_kind_2613_: *mut crate::leanh::LeanObject,
    mut v_p_2614_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2615_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2616_: u8,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(
        v_name_2612_,
        v_kind_2613_,
        v_anonymous_2616_,
        v_a_2617_,
        v_a_2618_,
        v_a_2619_,
        v_a_2620_,
    );
    return v___x_2622_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_formatter___boxed(
    mut v_name_2623_: *mut crate::leanh::LeanObject,
    mut v_kind_2624_: *mut crate::leanh::LeanObject,
    mut v_p_2625_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2626_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_a_2629_: *mut crate::leanh::LeanObject,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2633_: u8 = 0;
    let mut v_res_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2633_ = (crate::leanh::lean_unbox(v_anonymous_2627_) as u8);
    v_res_2634_ = l_Lake_Toml_litWithAntiquot_formatter(
        v_name_2623_,
        v_kind_2624_,
        v_p_2625_,
        v_trailingFn_2626_,
        v_anonymous_boxed_2633_,
        v_a_2628_,
        v_a_2629_,
        v_a_2630_,
        v_a_2631_,
    );
    crate::leanh::lean_dec(v_a_2631_);
    crate::leanh::lean_dec_ref(v_a_2630_);
    crate::leanh::lean_dec(v_a_2629_);
    crate::leanh::lean_dec_ref(v_a_2628_);
    crate::leanh::lean_dec_ref(v_trailingFn_2626_);
    crate::leanh::lean_dec_ref(v_p_2625_);
    return v_res_2634_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2640_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_2636_);
    return v___x_2640_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0___boxed(
    mut v___y_2641_: *mut crate::leanh::LeanObject,
    mut v___y_2642_: *mut crate::leanh::LeanObject,
    mut v___y_2643_: *mut crate::leanh::LeanObject,
    mut v___y_2644_: *mut crate::leanh::LeanObject,
    mut v___y_2645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2646_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___lam__0(
        v___y_2641_,
        v___y_2642_,
        v___y_2643_,
        v___y_2644_,
    );
    crate::leanh::lean_dec(v___y_2644_);
    crate::leanh::lean_dec_ref(v___y_2643_);
    crate::leanh::lean_dec(v___y_2642_);
    crate::leanh::lean_dec_ref(v___y_2641_);
    return v_res_2646_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
    mut v_name_2648_: *mut crate::leanh::LeanObject,
    mut v_kind_2649_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2650_: u8,
    mut v_a_2651_: *mut crate::leanh::LeanObject,
    mut v_a_2652_: *mut crate::leanh::LeanObject,
    mut v_a_2653_: *mut crate::leanh::LeanObject,
    mut v_a_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: u8 = 0;
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2656_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___closed__0;
    v___x_2657_ = 0;
    v___x_2658_ = crate::leanh::lean_box((v_anonymous_2650_) as usize);
    v___x_2659_ = crate::leanh::lean_box((v___x_2657_) as usize);
    v___x_2660_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_2660_, 0, v_name_2648_);
    crate::leanh::lean_closure_set(v___x_2660_, 1, v_kind_2649_);
    crate::leanh::lean_closure_set(v___x_2660_, 2, v___x_2658_);
    crate::leanh::lean_closure_set(v___x_2660_, 3, v___x_2659_);
    v___x_2661_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_2660_,
        v___f_2656_,
        v_a_2651_,
        v_a_2652_,
        v_a_2653_,
        v_a_2654_,
    );
    return v___x_2661_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer___redArg___boxed(
    mut v_name_2662_: *mut crate::leanh::LeanObject,
    mut v_kind_2663_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
    mut v_a_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2670_: u8 = 0;
    let mut v_res_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2670_ = (crate::leanh::lean_unbox(v_anonymous_2664_) as u8);
    v_res_2671_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v_name_2662_,
        v_kind_2663_,
        v_anonymous_boxed_2670_,
        v_a_2665_,
        v_a_2666_,
        v_a_2667_,
        v_a_2668_,
    );
    crate::leanh::lean_dec(v_a_2668_);
    crate::leanh::lean_dec_ref(v_a_2667_);
    crate::leanh::lean_dec(v_a_2666_);
    crate::leanh::lean_dec_ref(v_a_2665_);
    return v_res_2671_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer(
    mut v_name_2672_: *mut crate::leanh::LeanObject,
    mut v_kind_2673_: *mut crate::leanh::LeanObject,
    mut v_p_2674_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2675_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2676_: u8,
    mut v_a_2677_: *mut crate::leanh::LeanObject,
    mut v_a_2678_: *mut crate::leanh::LeanObject,
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(
        v_name_2672_,
        v_kind_2673_,
        v_anonymous_2676_,
        v_a_2677_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot_parenthesizer___boxed(
    mut v_name_2683_: *mut crate::leanh::LeanObject,
    mut v_kind_2684_: *mut crate::leanh::LeanObject,
    mut v_p_2685_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2686_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
    mut v_a_2691_: *mut crate::leanh::LeanObject,
    mut v_a_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2693_: u8 = 0;
    let mut v_res_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2693_ = (crate::leanh::lean_unbox(v_anonymous_2687_) as u8);
    v_res_2694_ = l_Lake_Toml_litWithAntiquot_parenthesizer(
        v_name_2683_,
        v_kind_2684_,
        v_p_2685_,
        v_trailingFn_2686_,
        v_anonymous_boxed_2693_,
        v_a_2688_,
        v_a_2689_,
        v_a_2690_,
        v_a_2691_,
    );
    crate::leanh::lean_dec(v_a_2691_);
    crate::leanh::lean_dec_ref(v_a_2690_);
    crate::leanh::lean_dec(v_a_2689_);
    crate::leanh::lean_dec_ref(v_a_2688_);
    crate::leanh::lean_dec_ref(v_trailingFn_2686_);
    crate::leanh::lean_dec_ref(v_p_2685_);
    return v_res_2694_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot(
    mut v_name_2695_: *mut crate::leanh::LeanObject,
    mut v_kind_2696_: *mut crate::leanh::LeanObject,
    mut v_p_2697_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2698_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2699_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2700_ = 0;
    crate::leanh::lean_inc(v_kind_2696_);
    v___x_2701_ =
        l_Lean_Parser_mkAntiquot(v_name_2695_, v_kind_2696_, v_anonymous_2699_, v___x_2700_);
    v___x_2702_ = l_Lake_Toml_lit(v_kind_2696_, v_p_2697_, v_trailingFn_2698_);
    v___x_2703_ = l_Lean_Parser_withAntiquot(v___x_2701_, v___x_2702_);
    return v___x_2703_;
}
pub unsafe fn l_Lake_Toml_litWithAntiquot___boxed(
    mut v_name_2704_: *mut crate::leanh::LeanObject,
    mut v_kind_2705_: *mut crate::leanh::LeanObject,
    mut v_p_2706_: *mut crate::leanh::LeanObject,
    mut v_trailingFn_2707_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2709_: u8 = 0;
    let mut v_res_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2709_ = (crate::leanh::lean_unbox(v_anonymous_2708_) as u8);
    v_res_2710_ = l_Lake_Toml_litWithAntiquot(
        v_name_2704_,
        v_kind_2705_,
        v_p_2706_,
        v_trailingFn_2707_,
        v_anonymous_boxed_2709_,
    );
    return v_res_2710_;
}
pub unsafe fn l_Lake_Toml_epsilon(
    mut v_fn_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = l_Lean_Parser_epsilonInfo;
    v___x_2713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2713_, 0, v___x_2712_);
    crate::leanh::lean_ctor_set(v___x_2713_, 1, v_fn_2711_);
    return v___x_2713_;
}
pub unsafe fn l_Lake_Toml_epsilon_formatter___redArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = crate::leanh::lean_box(0);
    v___x_2716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2716_, 0, v___x_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Lake_Toml_epsilon_formatter___redArg___boxed(
    mut v_a_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v_res_2718_;
}
pub unsafe fn l_Lake_Toml_epsilon_formatter(
    mut v_x_2719_: *mut crate::leanh::LeanObject,
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_2725_;
}
pub unsafe fn l_Lake_Toml_epsilon_formatter___boxed(
    mut v_x_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2732_ =
        l_Lake_Toml_epsilon_formatter(v_x_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
    crate::leanh::lean_dec(v_a_2730_);
    crate::leanh::lean_dec_ref(v_a_2729_);
    crate::leanh::lean_dec(v_a_2728_);
    crate::leanh::lean_dec_ref(v_a_2727_);
    crate::leanh::lean_dec_ref(v_x_2726_);
    return v_res_2732_;
}
pub unsafe fn l_Lake_Toml_epsilon_parenthesizer___redArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = crate::leanh::lean_box(0);
    v___x_2735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2734_);
    return v___x_2735_;
}
pub unsafe fn l_Lake_Toml_epsilon_parenthesizer___redArg___boxed(
    mut v_a_2736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2737_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v_res_2737_;
}
pub unsafe fn l_Lake_Toml_epsilon_parenthesizer(
    mut v_x_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_a_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2744_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_2744_;
}
pub unsafe fn l_Lake_Toml_epsilon_parenthesizer___boxed(
    mut v_x_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
    mut v_a_2748_: *mut crate::leanh::LeanObject,
    mut v_a_2749_: *mut crate::leanh::LeanObject,
    mut v_a_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ =
        l_Lake_Toml_epsilon_parenthesizer(v_x_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
    crate::leanh::lean_dec(v_a_2749_);
    crate::leanh::lean_dec_ref(v_a_2748_);
    crate::leanh::lean_dec(v_a_2747_);
    crate::leanh::lean_dec_ref(v_a_2746_);
    crate::leanh::lean_dec_ref(v_x_2745_);
    return v_res_2751_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(
    mut v_f_2752_: *mut crate::leanh::LeanObject,
    mut v_x_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut v_info_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_info_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v_v_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut v_unused_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2753_) {
                2 => {
                    v_info_2754_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                    v_val_2755_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2763_ = (!crate::leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2763_ == 0 {
                        v___x_2757_ = v_x_2753_;
                        v_isShared_2758_ = v_isSharedCheck_2763_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2755_);
                        crate::leanh::lean_inc(v_info_2754_);
                        crate::leanh::lean_dec(v_x_2753_);
                        v___x_2757_ = crate::leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2763_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_info_2764_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                    v_rawVal_2765_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                    v_val_2766_ = crate::leanh::lean_ctor_get(v_x_2753_, 2);
                    v_preresolved_2767_ = crate::leanh::lean_ctor_get(v_x_2753_, 3);
                    v_isSharedCheck_2775_ = (!crate::leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2775_ == 0 {
                        v___x_2769_ = v_x_2753_;
                        v_isShared_2770_ = v_isSharedCheck_2775_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_preresolved_2767_);
                        crate::leanh::lean_inc(v_val_2766_);
                        crate::leanh::lean_inc(v_rawVal_2765_);
                        crate::leanh::lean_inc(v_info_2764_);
                        crate::leanh::lean_dec(v_x_2753_);
                        v___x_2769_ = crate::leanh::lean_box(0);
                        v_isShared_2770_ = v_isSharedCheck_2775_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_info_2776_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                    v_kind_2777_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                    v_args_2778_ = crate::leanh::lean_ctor_get(v_x_2753_, 2);
                    v___x_2779_ = lean_array_get_size(v_args_2778_);
                    v___x_2780_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2781_ = lean_nat_sub(v___x_2779_, v___x_2780_);
                    v___x_2782_ = lean_nat_dec_lt(v___x_2781_, v___x_2779_);
                    if v___x_2782_ == 0 {
                        crate::leanh::lean_dec(v___x_2781_);
                        crate::leanh::lean_dec_ref(v_f_2752_);
                        return v_x_2753_;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_2778_);
                        crate::leanh::lean_inc(v_kind_2777_);
                        crate::leanh::lean_inc(v_info_2776_);
                        v_isSharedCheck_2794_ = (!crate::leanh::lean_is_exclusive(v_x_2753_)) as u8;
                        if v_isSharedCheck_2794_ == 0 {
                            v_unused_2795_ = crate::leanh::lean_ctor_get(v_x_2753_, 2);
                            crate::leanh::lean_dec(v_unused_2795_);
                            v_unused_2796_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                            crate::leanh::lean_dec(v_unused_2796_);
                            v_unused_2797_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                            crate::leanh::lean_dec(v_unused_2797_);
                            v___x_2784_ = v_x_2753_;
                            v_isShared_2785_ = v_isSharedCheck_2794_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2753_);
                            v___x_2784_ = crate::leanh::lean_box(0);
                            v_isShared_2785_ = v_isSharedCheck_2794_;
                            state = 5;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_f_2752_);
                    return v_x_2753_;
                }
            },
            1 => {
                v___x_2759_ = crate::leanh::lean_apply_1(v_f_2752_, v_info_2754_);
                if v_isShared_2758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2759_);
                    v___x_2761_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2762_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2762_, 1, v_val_2755_);
                    v___x_2761_ = v_reuseFailAlloc_2762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2761_;
            }
            3 => {
                v___x_2771_ = crate::leanh::lean_apply_1(v_f_2752_, v_info_2764_);
                if v_isShared_2770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2769_, 0, v___x_2771_);
                    v___x_2773_ = v___x_2769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_rawVal_2765_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_val_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 3, v_preresolved_2767_);
                    v___x_2773_ = v_reuseFailAlloc_2774_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2773_;
            }
            5 => {
                v_v_2786_ = lean_array_fget(v_args_2778_, v___x_2781_);
                v___x_2787_ = crate::leanh::lean_box(0);
                v_xs_x27_2788_ = lean_array_fset(v_args_2778_, v___x_2781_, v___x_2787_);
                v___x_2789_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo(
                    v_f_2752_, v_v_2786_,
                );
                v___x_2790_ = lean_array_fset(v_xs_x27_2788_, v___x_2781_, v___x_2789_);
                crate::leanh::lean_dec(v___x_2781_);
                if v_isShared_2785_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2784_, 2, v___x_2790_);
                    v___x_2792_ = v___x_2784_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2793_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_info_2776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_kind_2777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 2, v___x_2790_);
                    v___x_2792_ = v_reuseFailAlloc_2793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(
    mut v_stopPos_2798_: *mut crate::leanh::LeanObject,
    mut v_x_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_trailing_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v_str_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v_unused_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2799_) == 0 {
                    v_trailing_2800_ = crate::leanh::lean_ctor_get(v_x_2799_, 2);
                    v_leading_2801_ = crate::leanh::lean_ctor_get(v_x_2799_, 0);
                    v_pos_2802_ = crate::leanh::lean_ctor_get(v_x_2799_, 1);
                    v_endPos_2803_ = crate::leanh::lean_ctor_get(v_x_2799_, 3);
                    v_isSharedCheck_2820_ = (!crate::leanh::lean_is_exclusive(v_x_2799_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v___x_2805_ = v_x_2799_;
                        v_isShared_2806_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_2803_);
                        crate::leanh::lean_inc(v_trailing_2800_);
                        crate::leanh::lean_inc(v_pos_2802_);
                        crate::leanh::lean_inc(v_leading_2801_);
                        crate::leanh::lean_dec(v_x_2799_);
                        v___x_2805_ = crate::leanh::lean_box(0);
                        v_isShared_2806_ = v_isSharedCheck_2820_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stopPos_2798_);
                    return v_x_2799_;
                }
            }
            1 => {
                v_str_2807_ = crate::leanh::lean_ctor_get(v_trailing_2800_, 0);
                v_startPos_2808_ = crate::leanh::lean_ctor_get(v_trailing_2800_, 1);
                v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v_trailing_2800_)) as u8;
                if v_isSharedCheck_2818_ == 0 {
                    v_unused_2819_ = crate::leanh::lean_ctor_get(v_trailing_2800_, 2);
                    crate::leanh::lean_dec(v_unused_2819_);
                    v___x_2810_ = v_trailing_2800_;
                    v_isShared_2811_ = v_isSharedCheck_2818_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_startPos_2808_);
                    crate::leanh::lean_inc(v_str_2807_);
                    crate::leanh::lean_dec(v_trailing_2800_);
                    v___x_2810_ = crate::leanh::lean_box(0);
                    v_isShared_2811_ = v_isSharedCheck_2818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2810_, 2, v_stopPos_2798_);
                    v___x_2813_ = v___x_2810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_str_2807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 1, v_startPos_2808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 2, v_stopPos_2798_);
                    v___x_2813_ = v_reuseFailAlloc_2817_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2806_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2805_, 2, v___x_2813_);
                    v___x_2815_ = v___x_2805_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_leading_2801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_pos_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 2, v___x_2813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 3, v_endPos_2803_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(
    mut v_stopPos_2821_: *mut crate::leanh::LeanObject,
    mut v_x_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_info_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawVal_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_info_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2854_: u8 = 0;
    let mut v_v_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut v_unused_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2822_) {
                2 => {
                    v_info_2823_ = crate::leanh::lean_ctor_get(v_x_2822_, 0);
                    v_val_2824_ = crate::leanh::lean_ctor_get(v_x_2822_, 1);
                    v_isSharedCheck_2832_ = (!crate::leanh::lean_is_exclusive(v_x_2822_)) as u8;
                    if v_isSharedCheck_2832_ == 0 {
                        v___x_2826_ = v_x_2822_;
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2824_);
                        crate::leanh::lean_inc(v_info_2823_);
                        crate::leanh::lean_dec(v_x_2822_);
                        v___x_2826_ = crate::leanh::lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2832_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_info_2833_ = crate::leanh::lean_ctor_get(v_x_2822_, 0);
                    v_rawVal_2834_ = crate::leanh::lean_ctor_get(v_x_2822_, 1);
                    v_val_2835_ = crate::leanh::lean_ctor_get(v_x_2822_, 2);
                    v_preresolved_2836_ = crate::leanh::lean_ctor_get(v_x_2822_, 3);
                    v_isSharedCheck_2844_ = (!crate::leanh::lean_is_exclusive(v_x_2822_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v___x_2838_ = v_x_2822_;
                        v_isShared_2839_ = v_isSharedCheck_2844_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_preresolved_2836_);
                        crate::leanh::lean_inc(v_val_2835_);
                        crate::leanh::lean_inc(v_rawVal_2834_);
                        crate::leanh::lean_inc(v_info_2833_);
                        crate::leanh::lean_dec(v_x_2822_);
                        v___x_2838_ = crate::leanh::lean_box(0);
                        v_isShared_2839_ = v_isSharedCheck_2844_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_info_2845_ = crate::leanh::lean_ctor_get(v_x_2822_, 0);
                    v_kind_2846_ = crate::leanh::lean_ctor_get(v_x_2822_, 1);
                    v_args_2847_ = crate::leanh::lean_ctor_get(v_x_2822_, 2);
                    v___x_2848_ = lean_array_get_size(v_args_2847_);
                    v___x_2849_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2850_ = lean_nat_sub(v___x_2848_, v___x_2849_);
                    v___x_2851_ = lean_nat_dec_lt(v___x_2850_, v___x_2848_);
                    if v___x_2851_ == 0 {
                        crate::leanh::lean_dec(v___x_2850_);
                        crate::leanh::lean_dec(v_stopPos_2821_);
                        return v_x_2822_;
                    } else {
                        crate::leanh::lean_inc_ref(v_args_2847_);
                        crate::leanh::lean_inc(v_kind_2846_);
                        crate::leanh::lean_inc(v_info_2845_);
                        v_isSharedCheck_2863_ = (!crate::leanh::lean_is_exclusive(v_x_2822_)) as u8;
                        if v_isSharedCheck_2863_ == 0 {
                            v_unused_2864_ = crate::leanh::lean_ctor_get(v_x_2822_, 2);
                            crate::leanh::lean_dec(v_unused_2864_);
                            v_unused_2865_ = crate::leanh::lean_ctor_get(v_x_2822_, 1);
                            crate::leanh::lean_dec(v_unused_2865_);
                            v_unused_2866_ = crate::leanh::lean_ctor_get(v_x_2822_, 0);
                            crate::leanh::lean_dec(v_unused_2866_);
                            v___x_2853_ = v_x_2822_;
                            v_isShared_2854_ = v_isSharedCheck_2863_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2822_);
                            v___x_2853_ = crate::leanh::lean_box(0);
                            v_isShared_2854_ = v_isSharedCheck_2863_;
                            state = 5;
                            continue;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_stopPos_2821_);
                    return v_x_2822_;
                }
            },
            1 => {
                v___x_2828_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_2821_, v_info_2823_);
                if v_isShared_2827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2826_, 0, v___x_2828_);
                    v___x_2830_ = v___x_2826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 1, v_val_2824_);
                    v___x_2830_ = v_reuseFailAlloc_2831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2830_;
            }
            3 => {
                v___x_2840_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0___lam__0(v_stopPos_2821_, v_info_2833_);
                if v_isShared_2839_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2838_, 0, v___x_2840_);
                    v___x_2842_ = v___x_2838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_rawVal_2834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_val_2835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_preresolved_2836_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2842_;
            }
            5 => {
                v_v_2855_ = lean_array_fget(v_args_2847_, v___x_2850_);
                v___x_2856_ = crate::leanh::lean_box(0);
                v_xs_x27_2857_ = lean_array_fset(v_args_2847_, v___x_2850_, v___x_2856_);
                v___x_2858_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_stopPos_2821_, v_v_2855_);
                v___x_2859_ = lean_array_fset(v_xs_x27_2857_, v___x_2850_, v___x_2858_);
                crate::leanh::lean_dec(v___x_2850_);
                if v_isShared_2854_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2853_, 2, v___x_2859_);
                    v___x_2861_ = v___x_2853_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_info_2845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_kind_2846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 2, v___x_2859_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Toml_extendTrailingFn(
    mut v_p_2867_: *mut crate::leanh::LeanObject,
    mut v_c_2868_: *mut crate::leanh::LeanObject,
    mut v_s_2869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxStack_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_2870_ = crate::leanh::lean_apply_2(v_p_2867_, v_c_2868_, v_s_2869_);
    v_stxStack_2871_ = crate::leanh::lean_ctor_get(v_s_2870_, 0);
    crate::leanh::lean_inc_ref(v_stxStack_2871_);
    v_pos_2872_ = crate::leanh::lean_ctor_get(v_s_2870_, 2);
    crate::leanh::lean_inc(v_pos_2872_);
    v_tail_2873_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2871_);
    crate::leanh::lean_dec_ref(v_stxStack_2871_);
    v_s_2874_ = l_Lean_Parser_ParserState_popSyntax(v_s_2870_);
    v_tail_2875_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_modifyTailInfo___at___00Lake_Toml_extendTrailingFn_spec__0(v_pos_2872_, v_tail_2873_);
    v___x_2876_ = l_Lean_Parser_ParserState_pushSyntax(v_s_2874_, v_tail_2875_);
    return v___x_2876_;
}
pub unsafe fn l_Lake_Toml_trailing_formatter___redArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_2878_;
}
pub unsafe fn l_Lake_Toml_trailing_formatter___redArg___boxed(
    mut v_a_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2880_ = l_Lake_Toml_trailing_formatter___redArg();
    return v_res_2880_;
}
pub unsafe fn l_Lake_Toml_trailing_formatter(
    mut v_p_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
    mut v_a_2884_: *mut crate::leanh::LeanObject,
    mut v_a_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lake_Toml_epsilon_formatter___redArg();
    return v___x_2887_;
}
pub unsafe fn l_Lake_Toml_trailing_formatter___boxed(
    mut v_p_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
    mut v_a_2890_: *mut crate::leanh::LeanObject,
    mut v_a_2891_: *mut crate::leanh::LeanObject,
    mut v_a_2892_: *mut crate::leanh::LeanObject,
    mut v_a_2893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2894_ =
        l_Lake_Toml_trailing_formatter(v_p_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
    crate::leanh::lean_dec(v_a_2892_);
    crate::leanh::lean_dec_ref(v_a_2891_);
    crate::leanh::lean_dec(v_a_2890_);
    crate::leanh::lean_dec_ref(v_a_2889_);
    crate::leanh::lean_dec_ref(v_p_2888_);
    return v_res_2894_;
}
pub unsafe fn l_Lake_Toml_trailing_parenthesizer___redArg() -> *mut crate::leanh::LeanObject {
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_2896_;
}
pub unsafe fn l_Lake_Toml_trailing_parenthesizer___redArg___boxed(
    mut v_a_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2898_ = l_Lake_Toml_trailing_parenthesizer___redArg();
    return v_res_2898_;
}
pub unsafe fn l_Lake_Toml_trailing_parenthesizer(
    mut v_p_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2905_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
    return v___x_2905_;
}
pub unsafe fn l_Lake_Toml_trailing_parenthesizer___boxed(
    mut v_p_2906_: *mut crate::leanh::LeanObject,
    mut v_a_2907_: *mut crate::leanh::LeanObject,
    mut v_a_2908_: *mut crate::leanh::LeanObject,
    mut v_a_2909_: *mut crate::leanh::LeanObject,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2912_ =
        l_Lake_Toml_trailing_parenthesizer(v_p_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_);
    crate::leanh::lean_dec(v_a_2910_);
    crate::leanh::lean_dec_ref(v_a_2909_);
    crate::leanh::lean_dec(v_a_2908_);
    crate::leanh::lean_dec_ref(v_a_2907_);
    crate::leanh::lean_dec_ref(v_p_2906_);
    return v_res_2912_;
}
pub unsafe fn l_Lake_Toml_trailing(
    mut v_p_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_extendTrailingFn as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_2914_, 0, v_p_2913_);
    v___x_2915_ = l_Lean_Parser_epsilonInfo;
    v___x_2916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2916_, 0, v___x_2915_);
    crate::leanh::lean_ctor_set(v___x_2916_, 1, v___x_2914_);
    return v___x_2916_;
}
pub unsafe fn l_Lake_Toml_dynamicNode(
    mut v_p_2917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2918_ = l_Lake_Toml_atom___closed__2;
    v___x_2919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2919_, 0, v___x_2918_);
    crate::leanh::lean_ctor_set(v___x_2919_, 1, v_p_2917_);
    return v___x_2919_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_formatter___redArg(
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_atom_formatter_spec__0___redArg(
            v_a_2921_,
        );
    v_a_2926_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
    crate::leanh::lean_inc(v_a_2926_);
    crate::leanh::lean_dec_ref(v___x_2925_);
    v___x_2927_ = l_Lean_Syntax_getKind(v_a_2926_);
    v___x_2928_ = l_Lean_PrettyPrinter_Formatter_formatterForKindUnsafe(
        v___x_2927_,
        v_a_2920_,
        v_a_2921_,
        v_a_2922_,
        v_a_2923_,
    );
    return v___x_2928_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_formatter___redArg___boxed(
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_a_2931_: *mut crate::leanh::LeanObject,
    mut v_a_2932_: *mut crate::leanh::LeanObject,
    mut v_a_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2934_ =
        l_Lake_Toml_dynamicNode_formatter___redArg(v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_);
    crate::leanh::lean_dec(v_a_2932_);
    crate::leanh::lean_dec_ref(v_a_2931_);
    crate::leanh::lean_dec(v_a_2930_);
    crate::leanh::lean_dec_ref(v_a_2929_);
    return v_res_2934_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_formatter(
    mut v_x_2935_: *mut crate::leanh::LeanObject,
    mut v_a_2936_: *mut crate::leanh::LeanObject,
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2941_ =
        l_Lake_Toml_dynamicNode_formatter___redArg(v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
    return v___x_2941_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_formatter___boxed(
    mut v_x_2942_: *mut crate::leanh::LeanObject,
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ =
        l_Lake_Toml_dynamicNode_formatter(v_x_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_);
    crate::leanh::lean_dec(v_a_2946_);
    crate::leanh::lean_dec_ref(v_a_2945_);
    crate::leanh::lean_dec(v_a_2944_);
    crate::leanh::lean_dec_ref(v_a_2943_);
    crate::leanh::lean_dec_ref(v_x_2942_);
    return v_res_2948_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(
    mut v___y_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stxTrav_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = lean_st_ref_get(v___y_2949_);
    v_stxTrav_2952_ = crate::leanh::lean_ctor_get(v___x_2951_, 0);
    crate::leanh::lean_inc_ref(v_stxTrav_2952_);
    crate::leanh::lean_dec(v___x_2951_);
    v_cur_2953_ = crate::leanh::lean_ctor_get(v_stxTrav_2952_, 0);
    crate::leanh::lean_inc(v_cur_2953_);
    crate::leanh::lean_dec_ref(v_stxTrav_2952_);
    v___x_2954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2954_, 0, v_cur_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg___boxed(
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2957_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_2955_);
    crate::leanh::lean_dec(v___y_2955_);
    return v_res_2957_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2963_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v___y_2959_);
    return v___x_2963_;
}
pub unsafe fn l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___boxed(
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2969_ =
        l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0(
            v___y_2964_,
            v___y_2965_,
            v___y_2966_,
            v___y_2967_,
        );
    crate::leanh::lean_dec(v___y_2967_);
    crate::leanh::lean_dec_ref(v___y_2966_);
    crate::leanh::lean_dec(v___y_2965_);
    crate::leanh::lean_dec_ref(v___y_2964_);
    return v_res_2969_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_parenthesizer___redArg(
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = l_Lean_Syntax_MonadTraverser_getCur___at___00Lake_Toml_dynamicNode_parenthesizer_spec__0___redArg(v_a_2971_);
    v_a_2976_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
    crate::leanh::lean_inc(v_a_2976_);
    crate::leanh::lean_dec_ref(v___x_2975_);
    v___x_2977_ = l_Lean_Syntax_getKind(v_a_2976_);
    v___x_2978_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKindUnsafe(
        v___x_2977_,
        v_a_2970_,
        v_a_2971_,
        v_a_2972_,
        v_a_2973_,
    );
    return v___x_2978_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_parenthesizer___redArg___boxed(
    mut v_a_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
    mut v_a_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ =
        l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
    crate::leanh::lean_dec(v_a_2982_);
    crate::leanh::lean_dec_ref(v_a_2981_);
    crate::leanh::lean_dec(v_a_2980_);
    crate::leanh::lean_dec_ref(v_a_2979_);
    return v_res_2984_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_parenthesizer(
    mut v_x_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2991_ =
        l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_);
    return v___x_2991_;
}
pub unsafe fn l_Lake_Toml_dynamicNode_parenthesizer___boxed(
    mut v_x_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2998_ = l_Lake_Toml_dynamicNode_parenthesizer(
        v_x_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_,
    );
    crate::leanh::lean_dec(v_a_2996_);
    crate::leanh::lean_dec_ref(v_a_2995_);
    crate::leanh::lean_dec(v_a_2994_);
    crate::leanh::lean_dec_ref(v_a_2993_);
    crate::leanh::lean_dec_ref(v_x_2992_);
    return v_res_2998_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn(
    mut v_f_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_a_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_f_2999_);
    v___x_3002_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3002_, 0, v_f_2999_);
    v___x_3003_ = l_Lake_Toml_dynamicNode(v___x_3002_);
    v___x_3004_ = crate::leanh::lean_apply_1(v_f_2999_, v___x_3003_);
    v_fn_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 1);
    crate::leanh::lean_inc_ref(v_fn_3005_);
    crate::leanh::lean_dec_ref(v___x_3004_);
    v___x_3006_ = crate::leanh::lean_apply_2(v_fn_3005_, v_a_3000_, v_a_3001_);
    return v___x_3006_;
}
pub unsafe fn l_Lake_Toml_recNode_formatter___redArg(
    mut v_a_3007_: *mut crate::leanh::LeanObject,
    mut v_a_3008_: *mut crate::leanh::LeanObject,
    mut v_a_3009_: *mut crate::leanh::LeanObject,
    mut v_a_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3012_ =
        l_Lake_Toml_dynamicNode_formatter___redArg(v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_);
    return v___x_3012_;
}
pub unsafe fn l_Lake_Toml_recNode_formatter___redArg___boxed(
    mut v_a_3013_: *mut crate::leanh::LeanObject,
    mut v_a_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ =
        l_Lake_Toml_recNode_formatter___redArg(v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
    crate::leanh::lean_dec(v_a_3016_);
    crate::leanh::lean_dec_ref(v_a_3015_);
    crate::leanh::lean_dec(v_a_3014_);
    crate::leanh::lean_dec_ref(v_a_3013_);
    return v_res_3018_;
}
pub unsafe fn l_Lake_Toml_recNode_formatter(
    mut v_f_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
    mut v_a_3021_: *mut crate::leanh::LeanObject,
    mut v_a_3022_: *mut crate::leanh::LeanObject,
    mut v_a_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3025_ =
        l_Lake_Toml_dynamicNode_formatter___redArg(v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
    return v___x_3025_;
}
pub unsafe fn l_Lake_Toml_recNode_formatter___boxed(
    mut v_f_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3032_ =
        l_Lake_Toml_recNode_formatter(v_f_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_);
    crate::leanh::lean_dec(v_a_3030_);
    crate::leanh::lean_dec_ref(v_a_3029_);
    crate::leanh::lean_dec(v_a_3028_);
    crate::leanh::lean_dec_ref(v_a_3027_);
    crate::leanh::lean_dec_ref(v_f_3026_);
    return v_res_3032_;
}
pub unsafe fn l_Lake_Toml_recNode_parenthesizer___redArg(
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
    mut v_a_3035_: *mut crate::leanh::LeanObject,
    mut v_a_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3038_ =
        l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
    return v___x_3038_;
}
pub unsafe fn l_Lake_Toml_recNode_parenthesizer___redArg___boxed(
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
    mut v_a_3042_: *mut crate::leanh::LeanObject,
    mut v_a_3043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ =
        l_Lake_Toml_recNode_parenthesizer___redArg(v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
    crate::leanh::lean_dec(v_a_3042_);
    crate::leanh::lean_dec_ref(v_a_3041_);
    crate::leanh::lean_dec(v_a_3040_);
    crate::leanh::lean_dec_ref(v_a_3039_);
    return v_res_3044_;
}
pub unsafe fn l_Lake_Toml_recNode_parenthesizer(
    mut v_f_3045_: *mut crate::leanh::LeanObject,
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_a_3047_: *mut crate::leanh::LeanObject,
    mut v_a_3048_: *mut crate::leanh::LeanObject,
    mut v_a_3049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3051_ =
        l_Lake_Toml_dynamicNode_parenthesizer___redArg(v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
    return v___x_3051_;
}
pub unsafe fn l_Lake_Toml_recNode_parenthesizer___boxed(
    mut v_f_3052_: *mut crate::leanh::LeanObject,
    mut v_a_3053_: *mut crate::leanh::LeanObject,
    mut v_a_3054_: *mut crate::leanh::LeanObject,
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3058_ =
        l_Lake_Toml_recNode_parenthesizer(v_f_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
    crate::leanh::lean_dec(v_a_3056_);
    crate::leanh::lean_dec_ref(v_a_3055_);
    crate::leanh::lean_dec(v_a_3054_);
    crate::leanh::lean_dec_ref(v_a_3053_);
    crate::leanh::lean_dec_ref(v_f_3052_);
    return v_res_3058_;
}
pub unsafe fn l_Lake_Toml_recNode(
    mut v_f_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeFn as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3060_, 0, v_f_3059_);
    v___x_3061_ = l_Lake_Toml_dynamicNode(v___x_3060_);
    return v___x_3061_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(
    mut v_name_3062_: *mut crate::leanh::LeanObject,
    mut v_kind_3063_: *mut crate::leanh::LeanObject,
    mut v_f_3064_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3065_: u8,
    mut v_p_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3067_ = 1;
    crate::leanh::lean_inc(v_kind_3063_);
    v___x_3068_ =
        l_Lean_Parser_mkAntiquot(v_name_3062_, v_kind_3063_, v_anonymous_3065_, v___x_3067_);
    v___x_3069_ = crate::leanh::lean_apply_1(v_f_3064_, v_p_3066_);
    v___x_3070_ = l_Lean_Parser_withAntiquot(v___x_3068_, v___x_3069_);
    v___x_3071_ = l_Lean_Parser_withCache(v_kind_3063_, v___x_3070_);
    return v___x_3071_;
}
pub unsafe fn l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed(
    mut v_name_3072_: *mut crate::leanh::LeanObject,
    mut v_kind_3073_: *mut crate::leanh::LeanObject,
    mut v_f_3074_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3075_: *mut crate::leanh::LeanObject,
    mut v_p_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_3077_: u8 = 0;
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3077_ = (crate::leanh::lean_unbox(v_anonymous_3075_) as u8);
    v_res_3078_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go(
        v_name_3072_,
        v_kind_3073_,
        v_f_3074_,
        v_anonymous_boxed_3077_,
        v_p_3076_,
    );
    return v_res_3078_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot_formatter(
    mut v_name_3079_: *mut crate::leanh::LeanObject,
    mut v_kind_3080_: *mut crate::leanh::LeanObject,
    mut v_f_3081_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3082_: u8,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3088_: u8 = 0;
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = 1;
    v___x_3089_ = crate::leanh::lean_box((v_anonymous_3082_) as usize);
    v___x_3090_ = crate::leanh::lean_box((v___x_3088_) as usize);
    crate::leanh::lean_inc(v_kind_3080_);
    crate::leanh::lean_inc_ref(v_name_3079_);
    v___x_3091_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_formatter___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3091_, 0, v_name_3079_);
    crate::leanh::lean_closure_set(v___x_3091_, 1, v_kind_3080_);
    crate::leanh::lean_closure_set(v___x_3091_, 2, v___x_3089_);
    crate::leanh::lean_closure_set(v___x_3091_, 3, v___x_3090_);
    v___x_3092_ = crate::leanh::lean_box((v_anonymous_3082_) as usize);
    v___x_3093_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3093_, 0, v_name_3079_);
    crate::leanh::lean_closure_set(v___x_3093_, 1, v_kind_3080_);
    crate::leanh::lean_closure_set(v___x_3093_, 2, v_f_3081_);
    crate::leanh::lean_closure_set(v___x_3093_, 3, v___x_3092_);
    v___x_3094_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_recNode_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3094_, 0, v___x_3093_);
    v___x_3095_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3091_,
        v___x_3094_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
    );
    return v___x_3095_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot_formatter___boxed(
    mut v_name_3096_: *mut crate::leanh::LeanObject,
    mut v_kind_3097_: *mut crate::leanh::LeanObject,
    mut v_f_3098_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3099_: *mut crate::leanh::LeanObject,
    mut v_a_3100_: *mut crate::leanh::LeanObject,
    mut v_a_3101_: *mut crate::leanh::LeanObject,
    mut v_a_3102_: *mut crate::leanh::LeanObject,
    mut v_a_3103_: *mut crate::leanh::LeanObject,
    mut v_a_3104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_3105_: u8 = 0;
    let mut v_res_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3105_ = (crate::leanh::lean_unbox(v_anonymous_3099_) as u8);
    v_res_3106_ = l_Lake_Toml_recNodeWithAntiquot_formatter(
        v_name_3096_,
        v_kind_3097_,
        v_f_3098_,
        v_anonymous_boxed_3105_,
        v_a_3100_,
        v_a_3101_,
        v_a_3102_,
        v_a_3103_,
    );
    crate::leanh::lean_dec(v_a_3103_);
    crate::leanh::lean_dec_ref(v_a_3102_);
    crate::leanh::lean_dec(v_a_3101_);
    crate::leanh::lean_dec_ref(v_a_3100_);
    return v_res_3106_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot_parenthesizer(
    mut v_name_3107_: *mut crate::leanh::LeanObject,
    mut v_kind_3108_: *mut crate::leanh::LeanObject,
    mut v_f_3109_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3110_: u8,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3116_: u8 = 0;
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = 1;
    v___x_3117_ = crate::leanh::lean_box((v_anonymous_3110_) as usize);
    v___x_3118_ = crate::leanh::lean_box((v___x_3116_) as usize);
    crate::leanh::lean_inc(v_kind_3108_);
    crate::leanh::lean_inc_ref(v_name_3107_);
    v___x_3119_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3119_, 0, v_name_3107_);
    crate::leanh::lean_closure_set(v___x_3119_, 1, v_kind_3108_);
    crate::leanh::lean_closure_set(v___x_3119_, 2, v___x_3117_);
    crate::leanh::lean_closure_set(v___x_3119_, 3, v___x_3118_);
    v___x_3120_ = crate::leanh::lean_box((v_anonymous_3110_) as usize);
    v___x_3121_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3121_, 0, v_name_3107_);
    crate::leanh::lean_closure_set(v___x_3121_, 1, v_kind_3108_);
    crate::leanh::lean_closure_set(v___x_3121_, 2, v_f_3109_);
    crate::leanh::lean_closure_set(v___x_3121_, 3, v___x_3120_);
    v___x_3122_ = crate::leanh::lean_alloc_closure(
        l_Lake_Toml_recNode_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_3122_, 0, v___x_3121_);
    v___x_3123_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3119_,
        v___x_3122_,
        v_a_3111_,
        v_a_3112_,
        v_a_3113_,
        v_a_3114_,
    );
    return v___x_3123_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot_parenthesizer___boxed(
    mut v_name_3124_: *mut crate::leanh::LeanObject,
    mut v_kind_3125_: *mut crate::leanh::LeanObject,
    mut v_f_3126_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
    mut v_a_3132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_3133_: u8 = 0;
    let mut v_res_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3133_ = (crate::leanh::lean_unbox(v_anonymous_3127_) as u8);
    v_res_3134_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(
        v_name_3124_,
        v_kind_3125_,
        v_f_3126_,
        v_anonymous_boxed_3133_,
        v_a_3128_,
        v_a_3129_,
        v_a_3130_,
        v_a_3131_,
    );
    crate::leanh::lean_dec(v_a_3131_);
    crate::leanh::lean_dec_ref(v_a_3130_);
    crate::leanh::lean_dec(v_a_3129_);
    crate::leanh::lean_dec_ref(v_a_3128_);
    return v_res_3134_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot(
    mut v_name_3135_: *mut crate::leanh::LeanObject,
    mut v_kind_3136_: *mut crate::leanh::LeanObject,
    mut v_f_3137_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3138_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = 1;
    crate::leanh::lean_inc_n(v_kind_3136_, 2);
    crate::leanh::lean_inc_ref(v_name_3135_);
    v___x_3140_ =
        l_Lean_Parser_mkAntiquot(v_name_3135_, v_kind_3136_, v_anonymous_3138_, v___x_3139_);
    v___x_3141_ = crate::leanh::lean_box((v_anonymous_3138_) as usize);
    v___x_3142_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Toml_ParserUtil_0__Lake_Toml_recNodeWithAntiquot_go___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___x_3142_, 0, v_name_3135_);
    crate::leanh::lean_closure_set(v___x_3142_, 1, v_kind_3136_);
    crate::leanh::lean_closure_set(v___x_3142_, 2, v_f_3137_);
    crate::leanh::lean_closure_set(v___x_3142_, 3, v___x_3141_);
    v___x_3143_ = l_Lake_Toml_recNode(v___x_3142_);
    v___x_3144_ = l_Lean_Parser_withAntiquot(v___x_3140_, v___x_3143_);
    v___x_3145_ = l_Lean_Parser_withCache(v_kind_3136_, v___x_3144_);
    return v___x_3145_;
}
pub unsafe fn l_Lake_Toml_recNodeWithAntiquot___boxed(
    mut v_name_3146_: *mut crate::leanh::LeanObject,
    mut v_kind_3147_: *mut crate::leanh::LeanObject,
    mut v_f_3148_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_3150_: u8 = 0;
    let mut v_res_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3150_ = (crate::leanh::lean_unbox(v_anonymous_3149_) as u8);
    v_res_3151_ = l_Lake_Toml_recNodeWithAntiquot(
        v_name_3146_,
        v_kind_3147_,
        v_f_3148_,
        v_anonymous_boxed_3150_,
    );
    return v_res_3151_;
}
pub unsafe fn _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3159_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__0;
    v___x_3160_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3161_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3161_, 0, v___x_3160_);
    crate::leanh::lean_closure_set(v___x_3161_, 1, v___f_3159_);
    return v___x_3161_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_formatter___redArg(
    mut v_p_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3169_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4;
    v___x_3170_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3170_, 0, v___x_3168_);
    crate::leanh::lean_closure_set(v___x_3170_, 1, v_p_3162_);
    crate::leanh::lean_closure_set(v___x_3170_, 2, v___x_3169_);
    v___x_3171_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once),
        _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5,
    );
    v___x_3172_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(
        v___x_3170_,
        v___x_3171_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
        v_a_3166_,
    );
    return v___x_3172_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_formatter___redArg___boxed(
    mut v_p_3173_: *mut crate::leanh::LeanObject,
    mut v_a_3174_: *mut crate::leanh::LeanObject,
    mut v_a_3175_: *mut crate::leanh::LeanObject,
    mut v_a_3176_: *mut crate::leanh::LeanObject,
    mut v_a_3177_: *mut crate::leanh::LeanObject,
    mut v_a_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3179_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(
        v_p_3173_, v_a_3174_, v_a_3175_, v_a_3176_, v_a_3177_,
    );
    crate::leanh::lean_dec(v_a_3177_);
    crate::leanh::lean_dec_ref(v_a_3176_);
    crate::leanh::lean_dec(v_a_3175_);
    crate::leanh::lean_dec_ref(v_a_3174_);
    return v_res_3179_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_formatter(
    mut v_p_3180_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3181_: u8,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
    mut v_a_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_Lake_Toml_sepByLinebreak_formatter___redArg(
        v_p_3180_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_,
    );
    return v___x_3187_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_formatter___boxed(
    mut v_p_3188_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3189_: *mut crate::leanh::LeanObject,
    mut v_a_3190_: *mut crate::leanh::LeanObject,
    mut v_a_3191_: *mut crate::leanh::LeanObject,
    mut v_a_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3195_: u8 = 0;
    let mut v_res_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3195_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3189_) as u8);
    v_res_3196_ = l_Lake_Toml_sepByLinebreak_formatter(
        v_p_3188_,
        v_allowTrailingLinebreak_boxed_3195_,
        v_a_3190_,
        v_a_3191_,
        v_a_3192_,
        v_a_3193_,
    );
    crate::leanh::lean_dec(v_a_3193_);
    crate::leanh::lean_dec_ref(v_a_3192_);
    crate::leanh::lean_dec(v_a_3191_);
    crate::leanh::lean_dec_ref(v_a_3190_);
    return v_res_3196_;
}
pub unsafe fn _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3200_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__0;
    v___x_3201_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3202_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_3202_, 0, v___x_3201_);
    crate::leanh::lean_closure_set(v___x_3202_, 1, v___f_3200_);
    return v___x_3202_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(
    mut v_p_3203_: *mut crate::leanh::LeanObject,
    mut v_a_3204_: *mut crate::leanh::LeanObject,
    mut v_a_3205_: *mut crate::leanh::LeanObject,
    mut v_a_3206_: *mut crate::leanh::LeanObject,
    mut v_a_3207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3209_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3210_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1;
    v___x_3211_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3211_, 0, v___x_3209_);
    crate::leanh::lean_closure_set(v___x_3211_, 1, v_p_3203_);
    crate::leanh::lean_closure_set(v___x_3211_, 2, v___x_3210_);
    v___x_3212_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once),
        _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2,
    );
    v___x_3213_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(
        v___x_3211_,
        v___x_3212_,
        v_a_3204_,
        v_a_3205_,
        v_a_3206_,
        v_a_3207_,
    );
    return v___x_3213_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___boxed(
    mut v_p_3214_: *mut crate::leanh::LeanObject,
    mut v_a_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3220_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(
        v_p_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_,
    );
    crate::leanh::lean_dec(v_a_3218_);
    crate::leanh::lean_dec_ref(v_a_3217_);
    crate::leanh::lean_dec(v_a_3216_);
    crate::leanh::lean_dec_ref(v_a_3215_);
    return v_res_3220_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_parenthesizer(
    mut v_p_3221_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3222_: u8,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3228_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg(
        v_p_3221_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_,
    );
    return v___x_3228_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(
    mut v_p_3229_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3236_: u8 = 0;
    let mut v_res_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3236_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3230_) as u8);
    v_res_3237_ = l_Lake_Toml_sepByLinebreak_parenthesizer(
        v_p_3229_,
        v_allowTrailingLinebreak_boxed_3236_,
        v_a_3231_,
        v_a_3232_,
        v_a_3233_,
        v_a_3234_,
    );
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    crate::leanh::lean_dec(v_a_3232_);
    crate::leanh::lean_dec_ref(v_a_3231_);
    return v_res_3237_;
}
pub unsafe fn _init_l_Lake_Toml_sepByLinebreak___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3238_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__3;
    v___x_3239_ = l_Lean_Parser_symbol(v___x_3238_);
    return v___x_3239_;
}
pub unsafe fn _init_l_Lake_Toml_sepByLinebreak___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = l_Lake_Toml_sepByLinebreak___closed__1;
    v___x_3242_ = l_Lean_Parser_checkLinebreakBefore(v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn _init_l_Lake_Toml_sepByLinebreak___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_Parser_pushNone;
    v___x_3244_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__2_once),
        _init_l_Lake_Toml_sepByLinebreak___closed__2,
    );
    v___x_3245_ = l_Lean_Parser_andthen(v___x_3244_, v___x_3243_);
    return v___x_3245_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak(
    mut v_p_3246_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3247_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3249_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__0_once),
        _init_l_Lake_Toml_sepByLinebreak___closed__0,
    );
    v_p_3250_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_3248_, v_p_3246_, v___x_3249_);
    v___x_3251_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__3_once),
        _init_l_Lake_Toml_sepByLinebreak___closed__3,
    );
    v___x_3252_ =
        l_Lean_Parser_sepByNoAntiquot(v_p_3250_, v___x_3251_, v_allowTrailingLinebreak_3247_);
    return v___x_3252_;
}
pub unsafe fn l_Lake_Toml_sepByLinebreak___boxed(
    mut v_p_3253_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3255_: u8 = 0;
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3255_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3254_) as u8);
    v_res_3256_ = l_Lake_Toml_sepByLinebreak(v_p_3253_, v_allowTrailingLinebreak_boxed_3255_);
    return v_res_3256_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_formatter___redArg(
    mut v_p_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3264_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__4;
    v___x_3265_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3265_, 0, v___x_3263_);
    crate::leanh::lean_closure_set(v___x_3265_, 1, v_p_3257_);
    crate::leanh::lean_closure_set(v___x_3265_, 2, v___x_3264_);
    v___x_3266_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5_once),
        _init_l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__5,
    );
    v___x_3267_ = l_Lean_PrettyPrinter_Formatter_sepByNoAntiquot_formatter(
        v___x_3265_,
        v___x_3266_,
        v_a_3258_,
        v_a_3259_,
        v_a_3260_,
        v_a_3261_,
    );
    return v___x_3267_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_formatter___redArg___boxed(
    mut v_p_3268_: *mut crate::leanh::LeanObject,
    mut v_a_3269_: *mut crate::leanh::LeanObject,
    mut v_a_3270_: *mut crate::leanh::LeanObject,
    mut v_a_3271_: *mut crate::leanh::LeanObject,
    mut v_a_3272_: *mut crate::leanh::LeanObject,
    mut v_a_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3274_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(
        v_p_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_,
    );
    crate::leanh::lean_dec(v_a_3272_);
    crate::leanh::lean_dec_ref(v_a_3271_);
    crate::leanh::lean_dec(v_a_3270_);
    crate::leanh::lean_dec_ref(v_a_3269_);
    return v_res_3274_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_formatter(
    mut v_p_3275_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3276_: u8,
    mut v_a_3277_: *mut crate::leanh::LeanObject,
    mut v_a_3278_: *mut crate::leanh::LeanObject,
    mut v_a_3279_: *mut crate::leanh::LeanObject,
    mut v_a_3280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = l_Lake_Toml_sepBy1Linebreak_formatter___redArg(
        v_p_3275_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_,
    );
    return v___x_3282_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_formatter___boxed(
    mut v_p_3283_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3290_: u8 = 0;
    let mut v_res_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3290_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3284_) as u8);
    v_res_3291_ = l_Lake_Toml_sepBy1Linebreak_formatter(
        v_p_3283_,
        v_allowTrailingLinebreak_boxed_3290_,
        v_a_3285_,
        v_a_3286_,
        v_a_3287_,
        v_a_3288_,
    );
    crate::leanh::lean_dec(v_a_3288_);
    crate::leanh::lean_dec_ref(v_a_3287_);
    crate::leanh::lean_dec(v_a_3286_);
    crate::leanh::lean_dec_ref(v_a_3285_);
    return v_res_3291_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(
    mut v_p_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_a_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3299_ = l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__1;
    v___x_3300_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_withAntiquotSpliceAndSuffix_parenthesizer___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_3300_, 0, v___x_3298_);
    crate::leanh::lean_closure_set(v___x_3300_, 1, v_p_3292_);
    crate::leanh::lean_closure_set(v___x_3300_, 2, v___x_3299_);
    v___x_3301_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2_once),
        _init_l_Lake_Toml_sepByLinebreak_parenthesizer___redArg___closed__2,
    );
    v___x_3302_ = l_Lean_PrettyPrinter_Parenthesizer_sepByNoAntiquot_parenthesizer(
        v___x_3300_,
        v___x_3301_,
        v_a_3293_,
        v_a_3294_,
        v_a_3295_,
        v_a_3296_,
    );
    return v___x_3302_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg___boxed(
    mut v_p_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3309_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(
        v_p_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_,
    );
    crate::leanh::lean_dec(v_a_3307_);
    crate::leanh::lean_dec_ref(v_a_3306_);
    crate::leanh::lean_dec(v_a_3305_);
    crate::leanh::lean_dec_ref(v_a_3304_);
    return v_res_3309_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_parenthesizer(
    mut v_p_3310_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3311_: u8,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer___redArg(
        v_p_3310_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_,
    );
    return v___x_3317_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak_parenthesizer___boxed(
    mut v_p_3318_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
    mut v_a_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
    mut v_a_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3325_: u8 = 0;
    let mut v_res_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3325_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3319_) as u8);
    v_res_3326_ = l_Lake_Toml_sepBy1Linebreak_parenthesizer(
        v_p_3318_,
        v_allowTrailingLinebreak_boxed_3325_,
        v_a_3320_,
        v_a_3321_,
        v_a_3322_,
        v_a_3323_,
    );
    crate::leanh::lean_dec(v_a_3323_);
    crate::leanh::lean_dec_ref(v_a_3322_);
    crate::leanh::lean_dec(v_a_3321_);
    crate::leanh::lean_dec_ref(v_a_3320_);
    return v_res_3326_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak(
    mut v_p_3327_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3328_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Lake_Toml_sepByLinebreak_formatter___redArg___closed__2;
    v___x_3330_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__0_once),
        _init_l_Lake_Toml_sepByLinebreak___closed__0,
    );
    v_p_3331_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_3329_, v_p_3327_, v___x_3330_);
    v___x_3332_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__3),
        core::ptr::addr_of_mut!(l_Lake_Toml_sepByLinebreak___closed__3_once),
        _init_l_Lake_Toml_sepByLinebreak___closed__3,
    );
    v___x_3333_ =
        l_Lean_Parser_sepBy1NoAntiquot(v_p_3331_, v___x_3332_, v_allowTrailingLinebreak_3328_);
    return v___x_3333_;
}
pub unsafe fn l_Lake_Toml_sepBy1Linebreak___boxed(
    mut v_p_3334_: *mut crate::leanh::LeanObject,
    mut v_allowTrailingLinebreak_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowTrailingLinebreak_boxed_3336_: u8 = 0;
    let mut v_res_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowTrailingLinebreak_boxed_3336_ =
        (crate::leanh::lean_unbox(v_allowTrailingLinebreak_3335_) as u8);
    v_res_3337_ = l_Lake_Toml_sepBy1Linebreak(v_p_3334_, v_allowTrailingLinebreak_boxed_3336_);
    return v_res_3337_;
}
pub unsafe fn l_Lake_Toml_skipInsideQuotFn(
    mut v_p_3338_: *mut crate::leanh::LeanObject,
    mut v_c_3339_: *mut crate::leanh::LeanObject,
    mut v_s_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toCacheableParserContext_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotDepth_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: u8 = 0;
    v_toCacheableParserContext_3341_ = crate::leanh::lean_ctor_get(v_c_3339_, 2);
    v_quotDepth_3342_ = crate::leanh::lean_ctor_get(v_toCacheableParserContext_3341_, 1);
    v___x_3343_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3344_ = lean_nat_dec_lt(v___x_3343_, v_quotDepth_3342_);
    if v___x_3344_ == 0 {
        let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3345_ = crate::leanh::lean_apply_2(v_p_3338_, v_c_3339_, v_s_3340_);
        return v___x_3345_;
    } else {
        crate::leanh::lean_dec_ref(v_c_3339_);
        crate::leanh::lean_dec_ref(v_p_3338_);
        return v_s_3340_;
    }
}
pub unsafe fn l_Lake_Toml_skipInsideQuot_formatter(
    mut v_p_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
    mut v_a_3348_: *mut crate::leanh::LeanObject,
    mut v_a_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3350_);
    crate::leanh::lean_inc_ref(v_a_3349_);
    crate::leanh::lean_inc(v_a_3348_);
    crate::leanh::lean_inc_ref(v_a_3347_);
    v___x_3352_ = crate::leanh::lean_apply_5(
        v_p_3346_,
        v_a_3347_,
        v_a_3348_,
        v_a_3349_,
        v_a_3350_,
        crate::leanh::lean_box(0),
    );
    return v___x_3352_;
}
pub unsafe fn l_Lake_Toml_skipInsideQuot_formatter___boxed(
    mut v_p_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_a_3356_: *mut crate::leanh::LeanObject,
    mut v_a_3357_: *mut crate::leanh::LeanObject,
    mut v_a_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3359_ =
        l_Lake_Toml_skipInsideQuot_formatter(v_p_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
    crate::leanh::lean_dec(v_a_3357_);
    crate::leanh::lean_dec_ref(v_a_3356_);
    crate::leanh::lean_dec(v_a_3355_);
    crate::leanh::lean_dec_ref(v_a_3354_);
    return v_res_3359_;
}
pub unsafe fn l_Lake_Toml_skipInsideQuot_parenthesizer(
    mut v_p_3360_: *mut crate::leanh::LeanObject,
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3364_);
    crate::leanh::lean_inc_ref(v_a_3363_);
    crate::leanh::lean_inc(v_a_3362_);
    crate::leanh::lean_inc_ref(v_a_3361_);
    v___x_3366_ = crate::leanh::lean_apply_5(
        v_p_3360_,
        v_a_3361_,
        v_a_3362_,
        v_a_3363_,
        v_a_3364_,
        crate::leanh::lean_box(0),
    );
    return v___x_3366_;
}
pub unsafe fn l_Lake_Toml_skipInsideQuot_parenthesizer___boxed(
    mut v_p_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
    mut v_a_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lake_Toml_skipInsideQuot_parenthesizer(
        v_p_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_,
    );
    crate::leanh::lean_dec(v_a_3371_);
    crate::leanh::lean_dec_ref(v_a_3370_);
    crate::leanh::lean_dec(v_a_3369_);
    crate::leanh::lean_dec_ref(v_a_3368_);
    return v_res_3373_;
}
pub unsafe fn l_Lake_Toml_skipInsideQuot(
    mut v_p_3374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_info_3375_ = crate::leanh::lean_ctor_get(v_p_3374_, 0);
                v_fn_3376_ = crate::leanh::lean_ctor_get(v_p_3374_, 1);
                v_isSharedCheck_3384_ = (!crate::leanh::lean_is_exclusive(v_p_3374_)) as u8;
                if v_isSharedCheck_3384_ == 0 {
                    v___x_3378_ = v_p_3374_;
                    v_isShared_3379_ = v_isSharedCheck_3384_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fn_3376_);
                    crate::leanh::lean_inc(v_info_3375_);
                    crate::leanh::lean_dec(v_p_3374_);
                    v___x_3378_ = crate::leanh::lean_box(0);
                    v_isShared_3379_ = v_isSharedCheck_3384_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3380_ = crate::leanh::lean_alloc_closure(
                    l_Lake_Toml_skipInsideQuotFn as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3380_, 0, v_fn_3376_);
                if v_isShared_3379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3380_);
                    v___x_3382_ = v___x_3378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_info_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 1, v___x_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3382_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_ParserUtil(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_ParserUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_ParserUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_PrettyPrinter_Formatter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_ParserUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_ParserUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Toml_ParserUtil(builtin);
}
