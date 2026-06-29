// Lean compiler output
// Module: Lean.Parser
// Imports: Lean.Parser.Basic Lean.Parser.Level Lean.Parser.Term Lean.Parser.Tactic Lean.Parser.Command Lean.Parser.Module Lean.Parser.Syntax Lean.Parser.Do Lean.Parser.Tactic.Doc
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Parser::Basic::{
    initialize_Lean_Parser_Basic, l_Lean_Parser_andthen, l_Lean_Parser_atomic,
    l_Lean_Parser_checkColEq, l_Lean_Parser_checkColGe, l_Lean_Parser_checkColGt,
    l_Lean_Parser_checkLineEq, l_Lean_Parser_checkLinebreakBefore, l_Lean_Parser_checkNoWsBefore,
    l_Lean_Parser_checkWsBefore, l_Lean_Parser_lookahead, l_Lean_Parser_notFollowedBy,
    l_Lean_Parser_orelse, l_Lean_Parser_recover, l_Lean_Parser_withPosition,
    l_Lean_Parser_withoutForbidden, l_Lean_Parser_withoutPosition,
    runtime_initialize_Lean_Parser_Basic,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_getBinaryAlias___redArg, l_Lean_Parser_getConstAlias___redArg,
    l_Lean_Parser_getUnaryAlias___redArg, l_Lean_Parser_registerAlias,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_atomic_formatter___boxed, l_Lean_Parser_charLit,
    l_Lean_Parser_charLit_formatter___boxed, l_Lean_Parser_charLit_parenthesizer___boxed,
    l_Lean_Parser_hexnum, l_Lean_Parser_hygieneInfo, l_Lean_Parser_hygieneInfo_formatter___boxed,
    l_Lean_Parser_hygieneInfo_parenthesizer___boxed, l_Lean_Parser_ident,
    l_Lean_Parser_ident_formatter___boxed, l_Lean_Parser_ident_parenthesizer___boxed,
    l_Lean_Parser_many, l_Lean_Parser_many_formatter___boxed,
    l_Lean_Parser_many_parenthesizer___boxed, l_Lean_Parser_many1,
    l_Lean_Parser_many1_formatter___boxed, l_Lean_Parser_many1_parenthesizer___boxed,
    l_Lean_Parser_many1Indent_formatter___boxed, l_Lean_Parser_many1Indent_parenthesizer___boxed,
    l_Lean_Parser_manyIndent_formatter___boxed, l_Lean_Parser_manyIndent_parenthesizer___boxed,
    l_Lean_Parser_mkAntiquot_formatter, l_Lean_Parser_mkAntiquot_parenthesizer,
    l_Lean_Parser_nameLit, l_Lean_Parser_nameLit_formatter___boxed,
    l_Lean_Parser_nameLit_parenthesizer___boxed, l_Lean_Parser_nonReservedSymbol_formatter___boxed,
    l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, l_Lean_Parser_numLit,
    l_Lean_Parser_numLit_formatter___boxed, l_Lean_Parser_numLit_parenthesizer___boxed,
    l_Lean_Parser_optional, l_Lean_Parser_optional_formatter___boxed,
    l_Lean_Parser_optional_parenthesizer___boxed, l_Lean_Parser_rawIdent,
    l_Lean_Parser_rawIdent_formatter___boxed, l_Lean_Parser_rawIdent_parenthesizer___boxed,
    l_Lean_Parser_scientificLit, l_Lean_Parser_scientificLit_formatter___boxed,
    l_Lean_Parser_scientificLit_parenthesizer___boxed, l_Lean_Parser_sepBy_formatter___boxed,
    l_Lean_Parser_sepBy_parenthesizer___boxed, l_Lean_Parser_sepBy1_formatter___boxed,
    l_Lean_Parser_sepBy1_parenthesizer___boxed, l_Lean_Parser_strLit,
    l_Lean_Parser_strLit_formatter___boxed, l_Lean_Parser_strLit_parenthesizer___boxed,
    l_Lean_Parser_symbol_formatter___boxed, l_Lean_Parser_symbol_parenthesizer___boxed,
    l_Lean_Parser_unicodeSymbol_formatter___boxed,
    l_Lean_Parser_unicodeSymbol_parenthesizer___boxed,
    l_Lean_Parser_withPosition_formatter___boxed, l_Lean_Parser_withoutForbidden_formatter___boxed,
    l_Lean_Parser_withoutForbidden_parenthesizer___boxed,
    l_Lean_Parser_withoutPosition_formatter___boxed,
    l_Lean_Parser_withoutPosition_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Level::{
    initialize_Lean_Parser_Level, runtime_initialize_Lean_Parser_Level,
};
use crate::r#gen::Lean::Parser::Module::{
    initialize_Lean_Parser_Module, runtime_initialize_Lean_Parser_Module,
};
use crate::r#gen::Lean::Parser::StrInterpolation::l_Lean_Parser_interpolatedStr;
use crate::r#gen::Lean::Parser::Syntax::{
    initialize_Lean_Parser_Syntax, runtime_initialize_Lean_Parser_Syntax,
};
use crate::r#gen::Lean::Parser::Tactic::Doc::{
    initialize_Lean_Parser_Tactic_Doc, runtime_initialize_Lean_Parser_Tactic_Doc,
};
use crate::r#gen::Lean::Parser::Tactic::{
    initialize_Lean_Parser_Tactic, runtime_initialize_Lean_Parser_Tactic,
};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, l_Lean_Parser_Term_char_formatter,
    l_Lean_Parser_Term_char_formatter___boxed, l_Lean_Parser_Term_char_parenthesizer,
    l_Lean_Parser_Term_char_parenthesizer___boxed, l_Lean_Parser_Term_ident_formatter,
    l_Lean_Parser_Term_ident_formatter___boxed, l_Lean_Parser_Term_ident_parenthesizer,
    l_Lean_Parser_Term_ident_parenthesizer___boxed, l_Lean_Parser_Term_num_formatter,
    l_Lean_Parser_Term_num_formatter___boxed, l_Lean_Parser_Term_num_parenthesizer,
    l_Lean_Parser_Term_num_parenthesizer___boxed, l_Lean_Parser_Term_scientific_formatter,
    l_Lean_Parser_Term_scientific_formatter___boxed, l_Lean_Parser_Term_scientific_parenthesizer,
    l_Lean_Parser_Term_scientific_parenthesizer___boxed, l_Lean_Parser_Term_str_formatter,
    l_Lean_Parser_Term_str_formatter___boxed, l_Lean_Parser_Term_str_parenthesizer,
    l_Lean_Parser_Term_str_parenthesizer___boxed, runtime_initialize_Lean_Parser_Term,
};
use crate::r#gen::Lean::ParserCompiler::Attribute::l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg;
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_formatterAliasesRef,
    l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed,
    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_registerAlias,
    l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg,
    l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed,
    l_Lean_PrettyPrinter_combinatorFormatterAttribute, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef,
    l_Lean_PrettyPrinter_Parenthesizer_registerAlias,
    l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed,
    l_Lean_PrettyPrinter_combinatorParenthesizerAttribute,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [119, 115, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17759471530397124190 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 111, 116, 70, 111, 108, 108, 111, 119, 101, 100, 66, 121, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5889158377769613190 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8201135813669748762 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 99, 111, 118, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11451883528579887567 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2510058869824260539 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_recover as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12571085391447129896 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10645341263474320100 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_andthen as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,393173242845875278 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3598234189925664274 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_orelse as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 120, 110, 117, 109, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11510626477845773464 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11982095303264823988 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18163029821153688220 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2797157559945049776 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_interpolatedStr as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14298422259736409839 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [119, 105, 116, 104, 111, 117, 116, 70, 111, 114, 98, 105, 100, 100, 101, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2488176001515375140 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15810495650029311976 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1164644006045091397 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17508920231745936945 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17180264478054591478 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5944786210894363754 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withPosition as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withPosition_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 104, 101, 99, 107, 87, 115, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14787378393065436163 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 112, 97, 99, 101, 32, 98, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18170484695678750185 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2933775029743101773 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16727513630015613089 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12455907124956747413 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1Indent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1Indent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 110, 121, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12240491195871077271 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1556038599081871155 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_manyIndent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_manyIndent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 110, 121, 49, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17243740965612849207 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13889654070509321555 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 97, 110, 121, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2302572775315350313 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11576560798023578125 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 116, 111, 109, 105, 99, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4024150434455327032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11052958945290096852 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_atomic as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_atomic_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 111, 107, 97, 104, 101, 97, 100, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3382831200566926872 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15235553684503663412 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_lookahead as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 101, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7429455657892634123 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 104, 101, 99, 107, 76, 105, 110, 101, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14251682899144180462 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10019628956073368425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,304087650447937403 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 71, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4942254933594350711 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 71, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10876008678127703429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 71, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17597206043415342265 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 71, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17716280446251572173 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3737801725909557423 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_hygieneInfo_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_hygieneInfo_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 97, 119, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,930173994822296688 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11160707415378428636 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_rawIdent_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_rawIdent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12357768255797326360 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_ident_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_ident_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12926801259741997275 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11460878236439353836 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_scientificLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_scientificLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5949480926448383572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 109, 101, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8815315524667565364 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_nameLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_nameLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 104, 97, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16760301032635233067 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 104, 97, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11096140698252235337 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_charLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_charLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9232979286016572671 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3202936226761841983 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_strLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_strLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6110315075117401315 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 117, 109, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15973081547164711991 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_numLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_numLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 105, 110, 101, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4800675059916378954 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 104, 101, 99, 107, 76, 105, 110, 101, 98, 114, 101, 97, 107, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3297028327859390570 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 87, 115, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1581446985683836252 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [99, 104, 101, 99, 107, 78, 111, 87, 115, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8982410250343985142 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 111, 32, 115, 112, 97, 99, 101, 32, 98, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_ident_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject,6375785142665761018 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6741636008758929801 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject,738098606605637560 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_num_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject,6375785142665761018 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6443958244076462206 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject,6861786668853825883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_scientific_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject,6375785142665761018 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11724492440903985589 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject,18319288711560907444 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_char_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject,6375785142665761018 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1945590011008718296 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject,3745412335828369085 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_str_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut crate::leanh::LeanObject,6375785142665761018 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12532102953669115254 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut crate::leanh::LeanObject,929601914512300979 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_ident_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject,582838245365662195 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10890885640717993884 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject,5191661447043754805 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_num_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject,582838245365662195 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2835361733898899899 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject,12071238001331397246 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_scientific_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject,582838245365662195 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7590009743772624840 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject,1377634676658237465 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_char_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject,582838245365662195 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4774526234884175813 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject,745663875097992408 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_str_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject,582838245365662195 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4708573442450243427 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut crate::leanh::LeanObject,16580378683988055606 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_1808_);
    return v___x_1812_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1813_: *mut crate::leanh::LeanObject,
    mut v___y_1814_: *mut crate::leanh::LeanObject,
    mut v___y_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    crate::leanh::lean_dec(v___y_1816_);
    crate::leanh::lean_dec_ref(v___y_1815_);
    crate::leanh::lean_dec(v___y_1814_);
    crate::leanh::lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
    mut v___y_1822_: *mut crate::leanh::LeanObject,
    mut v___y_1823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = crate::leanh::lean_apply_5(
        v___y_1819_,
        v___y_1820_,
        v___y_1821_,
        v___y_1822_,
        v___y_1823_,
        crate::leanh::lean_box(0),
    );
    return v___x_1825_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1826_: *mut crate::leanh::LeanObject,
    mut v___y_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1832_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
    return v_res_1832_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_1835_ = l_Lean_Parser_checkColGe(v___x_1834_);
    return v___x_1835_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_1838_ = l_Lean_Parser_andthen(v___x_1837_, v___y_1836_);
    v___x_1839_ = l_Lean_Parser_many(v___x_1838_);
    v___x_1840_ = l_Lean_Parser_withPosition(v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1842_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_1843_ = l_Lean_Parser_andthen(v___x_1842_, v___y_1841_);
    v___x_1844_ = l_Lean_Parser_many1(v___x_1843_);
    v___x_1845_ = l_Lean_Parser_withPosition(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1847_);
    return v___x_1851_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
    crate::leanh::lean_dec(v___y_1855_);
    crate::leanh::lean_dec_ref(v___y_1854_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1864_ = crate::leanh::lean_apply_5(
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
        v___y_1861_,
        v___y_1862_,
        crate::leanh::lean_box(0),
    );
    return v___x_1864_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1871_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
    return v_res_1871_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v_x_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_1875_ = l_Lean_Parser_notFollowedBy(v_x_1873_, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_Parser_hexnum;
    v___x_1963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1967_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    return v___x_1967_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2052_ = l_Lean_Parser_checkWsBefore(v___x_2051_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2054_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2053_);
    return v___x_2054_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2197_ = l_Lean_Parser_checkLineEq(v___x_2196_);
    return v___x_2197_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    return v___x_2199_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    return v___x_2203_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2205_, 0, v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2214_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2215_ = l_Lean_Parser_checkColEq(v___x_2214_);
    return v___x_2215_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2216_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    return v___x_2217_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2220_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2222_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2223_, 0, v___x_2222_);
    return v___x_2223_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2232_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2233_ = l_Lean_Parser_checkColGe(v___x_2232_);
    return v___x_2233_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2234_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2235_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2235_, 0, v___x_2234_);
    return v___x_2235_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    return v___x_2239_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2241_, 0, v___x_2240_);
    return v___x_2241_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2251_ = l_Lean_Parser_checkColGt(v___x_2250_);
    return v___x_2251_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2252_);
    return v___x_2253_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2256_);
    return v___x_2257_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2258_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2259_, 0, v___x_2258_);
    return v___x_2259_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_Lean_Parser_hygieneInfo;
    v___x_2268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2284_ = l_Lean_Parser_rawIdent;
    v___x_2285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_Parser_ident;
    v___x_2300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2317_ = l_Lean_Parser_scientificLit;
    v___x_2318_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    return v___x_2318_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Parser_nameLit;
    v___x_2336_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2336_, 0, v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_Parser_charLit;
    v___x_2354_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lean_Parser_strLit;
    v___x_2372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2372_, 0, v___x_2371_);
    return v___x_2372_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = l_Lean_Parser_numLit;
    v___x_2390_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    return v___x_2390_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2415_ = l_Lean_Parser_checkLinebreakBefore(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2420_);
    return v___x_2421_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2423_, 0, v___x_2422_);
    return v___x_2423_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2434_ = l_Lean_Parser_checkNoWsBefore(v___x_2433_);
    return v___x_2434_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2436_, 0, v___x_2435_);
    return v___x_2436_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2442_, 0, v___x_2441_);
    return v___x_2442_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2443_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2444_, 0, v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2446_, 0, v___x_2445_);
    return v___x_2446_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2570_: u8 = 0;
    let mut v___y_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: u8 = 0;
    let mut v___y_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2601_: u8 = 0;
    let mut v___y_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: u8 = 0;
    let mut v___y_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2631_: u8 = 0;
    let mut v___y_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2448_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2564_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2565_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                v___x_2566_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2567_ = crate::leanh::lean_box(0);
                v___x_2659_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2851_ = l_Lean_Parser_registerAlias(
                    v___x_2448_,
                    v___x_2564_,
                    v___x_2565_,
                    v___x_2566_,
                    v___x_2659_,
                );
                if crate::leanh::lean_obj_tag(v___x_2851_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2851_, 1);
                    v___x_2852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2853_ =
                        l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2448_, v___x_2852_);
                    if crate::leanh::lean_obj_tag(v___x_2853_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2853_, 1);
                        v___x_2854_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2855_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                            v___x_2448_,
                            v___x_2854_,
                        );
                        v___y_2841_ = v___x_2855_;
                        state = 30;
                        continue;
                    } else {
                        v___y_2841_ = v___x_2853_;
                        state = 30;
                        continue;
                    }
                } else {
                    v___y_2841_ = v___x_2851_;
                    state = 30;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2451_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2451_, 1);
                    v___x_2452_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2453_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2454_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2455_ = crate::leanh::lean_box(0);
                    v___x_2456_ = l_Lean_Parser_registerAlias(
                        v___x_2452_,
                        v___x_2453_,
                        v___x_2454_,
                        v___x_2455_,
                        v___y_2450_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2456_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2456_, 1);
                        v___x_2457_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2458_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                            v___x_2452_,
                            v___x_2457_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2458_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2458_, 1);
                            v___x_2459_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2460_ = l_Lean_PrettyPrinter_Formatter_registerAlias(
                                v___x_2452_,
                                v___x_2459_,
                            );
                            return v___x_2460_;
                        } else {
                            return v___x_2458_;
                        }
                    } else {
                        return v___x_2456_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2450_);
                    return v___y_2451_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2463_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2463_, 1);
                    v___x_2464_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2465_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2466_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2467_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2462_);
                    v___x_2468_ = l_Lean_Parser_registerAlias(
                        v___x_2464_,
                        v___x_2465_,
                        v___x_2466_,
                        v___x_2467_,
                        v___y_2462_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2468_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2468_, 1);
                        v___x_2469_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2470_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2464_, v___x_2469_);
                        if crate::leanh::lean_obj_tag(v___x_2470_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2470_, 1);
                            v___x_2471_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2472_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2464_,
                                v___x_2471_,
                            );
                            v___y_2450_ = v___y_2462_;
                            v___y_2451_ = v___x_2472_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2450_ = v___y_2462_;
                            v___y_2451_ = v___x_2470_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_2450_ = v___y_2462_;
                        v___y_2451_ = v___x_2468_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2462_);
                    return v___y_2463_;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_2476_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2476_, 1);
                    v___x_2477_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2478_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2479_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2480_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2481_ = l_Lean_Parser_registerAlias(
                        v___x_2477_,
                        v___x_2478_,
                        v___x_2479_,
                        v___x_2480_,
                        v___y_2474_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2481_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2481_, 1);
                        v___x_2482_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2483_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2477_, v___x_2482_);
                        if crate::leanh::lean_obj_tag(v___x_2483_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2483_, 1);
                            v___x_2484_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2485_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2477_,
                                v___x_2484_,
                            );
                            v___y_2462_ = v___y_2475_;
                            v___y_2463_ = v___x_2485_;
                            state = 2;
                            continue;
                        } else {
                            v___y_2462_ = v___y_2475_;
                            v___y_2463_ = v___x_2483_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2462_ = v___y_2475_;
                        v___y_2463_ = v___x_2481_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2475_);
                    crate::leanh::lean_dec_ref(v___y_2474_);
                    return v___y_2476_;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_2489_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2489_, 1);
                    v___x_2490_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2491_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2492_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2493_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2488_);
                    v___x_2494_ = l_Lean_Parser_registerAlias(
                        v___x_2490_,
                        v___x_2491_,
                        v___x_2492_,
                        v___x_2493_,
                        v___y_2488_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2494_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2494_, 1);
                        v___x_2495_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2496_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2490_, v___x_2495_);
                        if crate::leanh::lean_obj_tag(v___x_2496_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2496_, 1);
                            v___x_2497_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2498_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2490_,
                                v___x_2497_,
                            );
                            v___y_2474_ = v___y_2487_;
                            v___y_2475_ = v___y_2488_;
                            v___y_2476_ = v___x_2498_;
                            state = 3;
                            continue;
                        } else {
                            v___y_2474_ = v___y_2487_;
                            v___y_2475_ = v___y_2488_;
                            v___y_2476_ = v___x_2496_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___y_2474_ = v___y_2487_;
                        v___y_2475_ = v___y_2488_;
                        v___y_2476_ = v___x_2494_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2488_);
                    crate::leanh::lean_dec_ref(v___y_2487_);
                    return v___y_2489_;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v___y_2502_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2502_, 1);
                    v___x_2503_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2504_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2505_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2506_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2501_);
                    v___x_2507_ = l_Lean_Parser_registerAlias(
                        v___x_2503_,
                        v___x_2504_,
                        v___x_2505_,
                        v___x_2506_,
                        v___y_2501_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2507_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2507_, 1);
                        v___x_2508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2509_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2503_, v___x_2508_);
                        if crate::leanh::lean_obj_tag(v___x_2509_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2509_, 1);
                            v___x_2510_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2511_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2503_,
                                v___x_2510_,
                            );
                            v___y_2487_ = v___y_2500_;
                            v___y_2488_ = v___y_2501_;
                            v___y_2489_ = v___x_2511_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2487_ = v___y_2500_;
                            v___y_2488_ = v___y_2501_;
                            v___y_2489_ = v___x_2509_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_2487_ = v___y_2500_;
                        v___y_2488_ = v___y_2501_;
                        v___y_2489_ = v___x_2507_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2501_);
                    crate::leanh::lean_dec_ref(v___y_2500_);
                    return v___y_2502_;
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_2515_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2515_, 1);
                    v___x_2516_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2517_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2518_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2519_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2514_);
                    v___x_2520_ = l_Lean_Parser_registerAlias(
                        v___x_2516_,
                        v___x_2517_,
                        v___x_2518_,
                        v___x_2519_,
                        v___y_2514_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2520_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2520_, 1);
                        v___x_2521_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2522_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2516_, v___x_2521_);
                        if crate::leanh::lean_obj_tag(v___x_2522_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2522_, 1);
                            v___x_2523_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2524_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2516_,
                                v___x_2523_,
                            );
                            v___y_2500_ = v___y_2513_;
                            v___y_2501_ = v___y_2514_;
                            v___y_2502_ = v___x_2524_;
                            state = 5;
                            continue;
                        } else {
                            v___y_2500_ = v___y_2513_;
                            v___y_2501_ = v___y_2514_;
                            v___y_2502_ = v___x_2522_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_2500_ = v___y_2513_;
                        v___y_2501_ = v___y_2514_;
                        v___y_2502_ = v___x_2520_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2514_);
                    crate::leanh::lean_dec_ref(v___y_2513_);
                    return v___y_2515_;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_2528_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2528_, 1);
                    v___x_2529_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2530_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2531_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2532_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2526_);
                    v___x_2533_ = l_Lean_Parser_registerAlias(
                        v___x_2529_,
                        v___x_2530_,
                        v___x_2531_,
                        v___x_2532_,
                        v___y_2526_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2533_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2533_, 1);
                        v___x_2534_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2535_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2529_, v___x_2534_);
                        if crate::leanh::lean_obj_tag(v___x_2535_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2535_, 1);
                            v___x_2536_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2537_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2529_,
                                v___x_2536_,
                            );
                            v___y_2513_ = v___y_2526_;
                            v___y_2514_ = v___y_2527_;
                            v___y_2515_ = v___x_2537_;
                            state = 6;
                            continue;
                        } else {
                            v___y_2513_ = v___y_2526_;
                            v___y_2514_ = v___y_2527_;
                            v___y_2515_ = v___x_2535_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_2513_ = v___y_2526_;
                        v___y_2514_ = v___y_2527_;
                        v___y_2515_ = v___x_2533_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2527_);
                    crate::leanh::lean_dec_ref(v___y_2526_);
                    return v___y_2528_;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_2541_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2541_, 1);
                    v___x_2542_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2543_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2544_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2545_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2539_);
                    v___x_2546_ = l_Lean_Parser_registerAlias(
                        v___x_2542_,
                        v___x_2543_,
                        v___x_2544_,
                        v___x_2545_,
                        v___y_2539_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2546_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2546_, 1);
                        v___x_2547_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2548_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2542_, v___x_2547_);
                        if crate::leanh::lean_obj_tag(v___x_2548_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2548_, 1);
                            v___x_2549_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2550_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2542_,
                                v___x_2549_,
                            );
                            v___y_2526_ = v___y_2539_;
                            v___y_2527_ = v___y_2540_;
                            v___y_2528_ = v___x_2550_;
                            state = 7;
                            continue;
                        } else {
                            v___y_2526_ = v___y_2539_;
                            v___y_2527_ = v___y_2540_;
                            v___y_2528_ = v___x_2548_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___y_2526_ = v___y_2539_;
                        v___y_2527_ = v___y_2540_;
                        v___y_2528_ = v___x_2546_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2540_);
                    crate::leanh::lean_dec_ref(v___y_2539_);
                    return v___y_2541_;
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v___y_2554_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2554_, 1);
                    v___x_2555_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2556_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2557_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2558_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2552_);
                    v___x_2559_ = l_Lean_Parser_registerAlias(
                        v___x_2555_,
                        v___x_2556_,
                        v___x_2557_,
                        v___x_2558_,
                        v___y_2552_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2559_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2559_, 1);
                        v___x_2560_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2561_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2555_, v___x_2560_);
                        if crate::leanh::lean_obj_tag(v___x_2561_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2561_, 1);
                            v___x_2562_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2563_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2555_,
                                v___x_2562_,
                            );
                            v___y_2539_ = v___y_2552_;
                            v___y_2540_ = v___y_2553_;
                            v___y_2541_ = v___x_2563_;
                            state = 8;
                            continue;
                        } else {
                            v___y_2539_ = v___y_2552_;
                            v___y_2540_ = v___y_2553_;
                            v___y_2541_ = v___x_2561_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___y_2539_ = v___y_2552_;
                        v___y_2540_ = v___y_2553_;
                        v___y_2541_ = v___x_2559_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2553_);
                    crate::leanh::lean_dec_ref(v___y_2552_);
                    return v___y_2554_;
                }
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_2573_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2573_, 1);
                    v___x_2574_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2575_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2576_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2577_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc(v___y_2572_);
                    v___x_2578_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2578_, 0, v___x_2567_);
                    crate::leanh::lean_ctor_set(v___x_2578_, 1, v___y_2572_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2578_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___y_2570_,
                    );
                    v___x_2579_ = l_Lean_Parser_registerAlias(
                        v___x_2574_,
                        v___x_2575_,
                        v___x_2576_,
                        v___x_2577_,
                        v___x_2578_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2579_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2580_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2581_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2574_, v___x_2580_);
                        if crate::leanh::lean_obj_tag(v___x_2581_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2581_, 1);
                            v___x_2582_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2583_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2574_,
                                v___x_2582_,
                            );
                            v___y_2552_ = v___y_2569_;
                            v___y_2553_ = v___y_2571_;
                            v___y_2554_ = v___x_2583_;
                            state = 9;
                            continue;
                        } else {
                            v___y_2552_ = v___y_2569_;
                            v___y_2553_ = v___y_2571_;
                            v___y_2554_ = v___x_2581_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___y_2552_ = v___y_2569_;
                        v___y_2553_ = v___y_2571_;
                        v___y_2554_ = v___x_2579_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2571_);
                    crate::leanh::lean_dec_ref(v___y_2569_);
                    return v___y_2573_;
                }
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_2589_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2589_, 1);
                    v___x_2590_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2591_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2592_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2593_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2588_);
                    v___x_2594_ = l_Lean_Parser_registerAlias(
                        v___x_2590_,
                        v___x_2591_,
                        v___x_2592_,
                        v___x_2593_,
                        v___y_2588_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2594_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2594_, 1);
                        v___x_2595_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2596_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2590_, v___x_2595_);
                        if crate::leanh::lean_obj_tag(v___x_2596_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2596_, 1);
                            v___x_2597_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2598_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2590_,
                                v___x_2597_,
                            );
                            v___y_2569_ = v___y_2585_;
                            v___y_2570_ = v___y_2586_;
                            v___y_2571_ = v___y_2588_;
                            v___y_2572_ = v___y_2587_;
                            v___y_2573_ = v___x_2598_;
                            state = 10;
                            continue;
                        } else {
                            v___y_2569_ = v___y_2585_;
                            v___y_2570_ = v___y_2586_;
                            v___y_2571_ = v___y_2588_;
                            v___y_2572_ = v___y_2587_;
                            v___y_2573_ = v___x_2596_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v___y_2569_ = v___y_2585_;
                        v___y_2570_ = v___y_2586_;
                        v___y_2571_ = v___y_2588_;
                        v___y_2572_ = v___y_2587_;
                        v___y_2573_ = v___x_2594_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2588_);
                    crate::leanh::lean_dec_ref(v___y_2585_);
                    return v___y_2589_;
                }
            }
            12 => {
                if crate::leanh::lean_obj_tag(v___y_2604_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2604_, 1);
                    v___x_2605_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2606_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2607_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2608_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2603_);
                    v___x_2609_ = l_Lean_Parser_registerAlias(
                        v___x_2605_,
                        v___x_2606_,
                        v___x_2607_,
                        v___x_2608_,
                        v___y_2603_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2609_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2609_, 1);
                        v___x_2610_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2611_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2605_, v___x_2610_);
                        if crate::leanh::lean_obj_tag(v___x_2611_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2611_, 1);
                            v___x_2612_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2613_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2605_,
                                v___x_2612_,
                            );
                            v___y_2585_ = v___y_2600_;
                            v___y_2586_ = v___y_2601_;
                            v___y_2587_ = v___y_2602_;
                            v___y_2588_ = v___y_2603_;
                            v___y_2589_ = v___x_2613_;
                            state = 11;
                            continue;
                        } else {
                            v___y_2585_ = v___y_2600_;
                            v___y_2586_ = v___y_2601_;
                            v___y_2587_ = v___y_2602_;
                            v___y_2588_ = v___y_2603_;
                            v___y_2589_ = v___x_2611_;
                            state = 11;
                            continue;
                        }
                    } else {
                        v___y_2585_ = v___y_2600_;
                        v___y_2586_ = v___y_2601_;
                        v___y_2587_ = v___y_2602_;
                        v___y_2588_ = v___y_2603_;
                        v___y_2589_ = v___x_2609_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2603_);
                    crate::leanh::lean_dec_ref(v___y_2600_);
                    return v___y_2604_;
                }
            }
            13 => {
                if crate::leanh::lean_obj_tag(v___y_2619_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2619_, 1);
                    v___x_2620_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2621_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2622_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2623_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2618_);
                    v___x_2624_ = l_Lean_Parser_registerAlias(
                        v___x_2620_,
                        v___x_2621_,
                        v___x_2622_,
                        v___x_2623_,
                        v___y_2618_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2624_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2624_, 1);
                        v___x_2625_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2626_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2620_, v___x_2625_);
                        if crate::leanh::lean_obj_tag(v___x_2626_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2626_, 1);
                            v___x_2627_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2628_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2620_,
                                v___x_2627_,
                            );
                            v___y_2600_ = v___y_2615_;
                            v___y_2601_ = v___y_2616_;
                            v___y_2602_ = v___y_2617_;
                            v___y_2603_ = v___y_2618_;
                            v___y_2604_ = v___x_2628_;
                            state = 12;
                            continue;
                        } else {
                            v___y_2600_ = v___y_2615_;
                            v___y_2601_ = v___y_2616_;
                            v___y_2602_ = v___y_2617_;
                            v___y_2603_ = v___y_2618_;
                            v___y_2604_ = v___x_2626_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___y_2600_ = v___y_2615_;
                        v___y_2601_ = v___y_2616_;
                        v___y_2602_ = v___y_2617_;
                        v___y_2603_ = v___y_2618_;
                        v___y_2604_ = v___x_2624_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2618_);
                    crate::leanh::lean_dec_ref(v___y_2615_);
                    return v___y_2619_;
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v___y_2634_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2634_, 1);
                    v___x_2635_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2636_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2637_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2638_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2633_);
                    v___x_2639_ = l_Lean_Parser_registerAlias(
                        v___x_2635_,
                        v___x_2636_,
                        v___x_2637_,
                        v___x_2638_,
                        v___y_2633_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2639_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2639_, 1);
                        v___x_2640_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2641_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2635_, v___x_2640_);
                        if crate::leanh::lean_obj_tag(v___x_2641_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2641_, 1);
                            v___x_2642_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2643_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2635_,
                                v___x_2642_,
                            );
                            v___y_2615_ = v___y_2630_;
                            v___y_2616_ = v___y_2631_;
                            v___y_2617_ = v___y_2632_;
                            v___y_2618_ = v___y_2633_;
                            v___y_2619_ = v___x_2643_;
                            state = 13;
                            continue;
                        } else {
                            v___y_2615_ = v___y_2630_;
                            v___y_2616_ = v___y_2631_;
                            v___y_2617_ = v___y_2632_;
                            v___y_2618_ = v___y_2633_;
                            v___y_2619_ = v___x_2641_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___y_2615_ = v___y_2630_;
                        v___y_2616_ = v___y_2631_;
                        v___y_2617_ = v___y_2632_;
                        v___y_2618_ = v___y_2633_;
                        v___y_2619_ = v___x_2639_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2633_);
                    crate::leanh::lean_dec_ref(v___y_2630_);
                    return v___y_2634_;
                }
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_2647_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2647_, 1);
                    v___x_2648_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2649_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2650_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2651_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2652_ = 0;
                    v___x_2653_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2654_ = l_Lean_Parser_registerAlias(
                        v___x_2648_,
                        v___x_2649_,
                        v___x_2650_,
                        v___x_2651_,
                        v___x_2653_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2654_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2654_, 1);
                        v___x_2655_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2656_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2648_, v___x_2655_);
                        if crate::leanh::lean_obj_tag(v___x_2656_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2656_, 1);
                            v___x_2657_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2658_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2648_,
                                v___x_2657_,
                            );
                            v___y_2630_ = v___x_2653_;
                            v___y_2631_ = v___x_2652_;
                            v___y_2632_ = v___y_2645_;
                            v___y_2633_ = v___y_2646_;
                            v___y_2634_ = v___x_2658_;
                            state = 14;
                            continue;
                        } else {
                            v___y_2630_ = v___x_2653_;
                            v___y_2631_ = v___x_2652_;
                            v___y_2632_ = v___y_2645_;
                            v___y_2633_ = v___y_2646_;
                            v___y_2634_ = v___x_2656_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___y_2630_ = v___x_2653_;
                        v___y_2631_ = v___x_2652_;
                        v___y_2632_ = v___y_2645_;
                        v___y_2633_ = v___y_2646_;
                        v___y_2634_ = v___x_2654_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2646_);
                    return v___y_2647_;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_2663_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2663_, 1);
                    v___x_2664_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2665_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2666_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2667_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2668_ = l_Lean_Parser_registerAlias(
                        v___x_2664_,
                        v___x_2665_,
                        v___x_2666_,
                        v___x_2667_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2668_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2668_, 1);
                        v___x_2669_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2670_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2664_, v___x_2669_);
                        if crate::leanh::lean_obj_tag(v___x_2670_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2670_, 1);
                            v___x_2671_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2672_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2664_,
                                v___x_2671_,
                            );
                            v___y_2645_ = v___y_2662_;
                            v___y_2646_ = v___y_2661_;
                            v___y_2647_ = v___x_2672_;
                            state = 15;
                            continue;
                        } else {
                            v___y_2645_ = v___y_2662_;
                            v___y_2646_ = v___y_2661_;
                            v___y_2647_ = v___x_2670_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___y_2645_ = v___y_2662_;
                        v___y_2646_ = v___y_2661_;
                        v___y_2647_ = v___x_2668_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2661_);
                    return v___y_2663_;
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v___y_2676_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2676_, 1);
                    v___x_2677_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2678_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2680_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2681_ = l_Lean_Parser_registerAlias(
                        v___x_2677_,
                        v___x_2678_,
                        v___x_2679_,
                        v___x_2680_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2681_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2681_, 1);
                        v___x_2682_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2683_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2677_, v___x_2682_);
                        if crate::leanh::lean_obj_tag(v___x_2683_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2683_, 1);
                            v___x_2684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2685_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2677_,
                                v___x_2684_,
                            );
                            v___y_2661_ = v___y_2675_;
                            v___y_2662_ = v___y_2674_;
                            v___y_2663_ = v___x_2685_;
                            state = 16;
                            continue;
                        } else {
                            v___y_2661_ = v___y_2675_;
                            v___y_2662_ = v___y_2674_;
                            v___y_2663_ = v___x_2683_;
                            state = 16;
                            continue;
                        }
                    } else {
                        v___y_2661_ = v___y_2675_;
                        v___y_2662_ = v___y_2674_;
                        v___y_2663_ = v___x_2681_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2675_);
                    return v___y_2676_;
                }
            }
            18 => {
                if crate::leanh::lean_obj_tag(v___y_2689_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2689_, 1);
                    v___x_2690_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2691_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2693_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2694_ = l_Lean_Parser_registerAlias(
                        v___x_2690_,
                        v___x_2691_,
                        v___x_2692_,
                        v___x_2693_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2694_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2694_, 1);
                        v___x_2695_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2696_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2690_, v___x_2695_);
                        if crate::leanh::lean_obj_tag(v___x_2696_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2696_, 1);
                            v___x_2697_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2698_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2690_,
                                v___x_2697_,
                            );
                            v___y_2674_ = v___y_2688_;
                            v___y_2675_ = v___y_2687_;
                            v___y_2676_ = v___x_2698_;
                            state = 17;
                            continue;
                        } else {
                            v___y_2674_ = v___y_2688_;
                            v___y_2675_ = v___y_2687_;
                            v___y_2676_ = v___x_2696_;
                            state = 17;
                            continue;
                        }
                    } else {
                        v___y_2674_ = v___y_2688_;
                        v___y_2675_ = v___y_2687_;
                        v___y_2676_ = v___x_2694_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2687_);
                    return v___y_2689_;
                }
            }
            19 => {
                if crate::leanh::lean_obj_tag(v___y_2702_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2702_, 1);
                    v___x_2703_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2704_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2705_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2706_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2707_ = l_Lean_Parser_registerAlias(
                        v___x_2703_,
                        v___x_2704_,
                        v___x_2705_,
                        v___x_2706_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2707_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2707_, 1);
                        v___x_2708_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2709_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2703_, v___x_2708_);
                        if crate::leanh::lean_obj_tag(v___x_2709_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2709_, 1);
                            v___x_2710_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2711_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2703_,
                                v___x_2710_,
                            );
                            v___y_2687_ = v___y_2701_;
                            v___y_2688_ = v___y_2700_;
                            v___y_2689_ = v___x_2711_;
                            state = 18;
                            continue;
                        } else {
                            v___y_2687_ = v___y_2701_;
                            v___y_2688_ = v___y_2700_;
                            v___y_2689_ = v___x_2709_;
                            state = 18;
                            continue;
                        }
                    } else {
                        v___y_2687_ = v___y_2701_;
                        v___y_2688_ = v___y_2700_;
                        v___y_2689_ = v___x_2707_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2701_);
                    return v___y_2702_;
                }
            }
            20 => {
                if crate::leanh::lean_obj_tag(v___y_2715_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2715_, 1);
                    v___x_2716_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2717_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2718_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2719_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2720_ = l_Lean_Parser_registerAlias(
                        v___x_2716_,
                        v___x_2717_,
                        v___x_2718_,
                        v___x_2719_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2720_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2720_, 1);
                        v___x_2721_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2722_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2716_, v___x_2721_);
                        if crate::leanh::lean_obj_tag(v___x_2722_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2722_, 1);
                            v___x_2723_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2724_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2716_,
                                v___x_2723_,
                            );
                            v___y_2700_ = v___y_2714_;
                            v___y_2701_ = v___y_2713_;
                            v___y_2702_ = v___x_2724_;
                            state = 19;
                            continue;
                        } else {
                            v___y_2700_ = v___y_2714_;
                            v___y_2701_ = v___y_2713_;
                            v___y_2702_ = v___x_2722_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v___y_2700_ = v___y_2714_;
                        v___y_2701_ = v___y_2713_;
                        v___y_2702_ = v___x_2720_;
                        state = 19;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2713_);
                    return v___y_2715_;
                }
            }
            21 => {
                if crate::leanh::lean_obj_tag(v___y_2728_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2728_, 1);
                    v___x_2729_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2730_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2731_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2732_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2727_);
                    v___x_2733_ = l_Lean_Parser_registerAlias(
                        v___x_2729_,
                        v___x_2730_,
                        v___x_2731_,
                        v___x_2732_,
                        v___y_2727_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2733_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2733_, 1);
                        v___x_2734_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2735_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2729_, v___x_2734_);
                        if crate::leanh::lean_obj_tag(v___x_2735_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2735_, 1);
                            v___x_2736_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2737_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2729_,
                                v___x_2736_,
                            );
                            v___y_2713_ = v___y_2727_;
                            v___y_2714_ = v___y_2726_;
                            v___y_2715_ = v___x_2737_;
                            state = 20;
                            continue;
                        } else {
                            v___y_2713_ = v___y_2727_;
                            v___y_2714_ = v___y_2726_;
                            v___y_2715_ = v___x_2735_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___y_2713_ = v___y_2727_;
                        v___y_2714_ = v___y_2726_;
                        v___y_2715_ = v___x_2733_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2727_);
                    return v___y_2728_;
                }
            }
            22 => {
                if crate::leanh::lean_obj_tag(v___y_2742_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2742_, 1);
                    v___x_2743_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2744_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    crate::leanh::lean_inc_ref(v___y_2741_);
                    v___x_2746_ = l_Lean_Parser_registerAlias(
                        v___x_2743_,
                        v___x_2744_,
                        v___x_2745_,
                        v___y_2739_,
                        v___y_2741_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2746_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2746_, 1);
                        v___x_2747_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2748_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2743_, v___x_2747_);
                        if crate::leanh::lean_obj_tag(v___x_2748_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2748_, 1);
                            v___x_2749_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2750_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2743_,
                                v___x_2749_,
                            );
                            v___y_2726_ = v___y_2740_;
                            v___y_2727_ = v___y_2741_;
                            v___y_2728_ = v___x_2750_;
                            state = 21;
                            continue;
                        } else {
                            v___y_2726_ = v___y_2740_;
                            v___y_2727_ = v___y_2741_;
                            v___y_2728_ = v___x_2748_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v___y_2726_ = v___y_2740_;
                        v___y_2727_ = v___y_2741_;
                        v___y_2728_ = v___x_2746_;
                        state = 21;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2741_);
                    crate::leanh::lean_dec(v___y_2739_);
                    return v___y_2742_;
                }
            }
            23 => {
                if crate::leanh::lean_obj_tag(v___y_2754_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2754_, 1);
                    v___x_2755_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2756_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2758_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2752_);
                    v___x_2759_ = l_Lean_Parser_registerAlias(
                        v___x_2755_,
                        v___x_2756_,
                        v___x_2757_,
                        v___x_2758_,
                        v___y_2752_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2759_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2759_, 1);
                        v___x_2760_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2761_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2755_, v___x_2760_);
                        if crate::leanh::lean_obj_tag(v___x_2761_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2761_, 1);
                            v___x_2762_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2763_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2755_,
                                v___x_2762_,
                            );
                            v___y_2739_ = v___x_2758_;
                            v___y_2740_ = v___y_2753_;
                            v___y_2741_ = v___y_2752_;
                            v___y_2742_ = v___x_2763_;
                            state = 22;
                            continue;
                        } else {
                            v___y_2739_ = v___x_2758_;
                            v___y_2740_ = v___y_2753_;
                            v___y_2741_ = v___y_2752_;
                            v___y_2742_ = v___x_2761_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___y_2739_ = v___x_2758_;
                        v___y_2740_ = v___y_2753_;
                        v___y_2741_ = v___y_2752_;
                        v___y_2742_ = v___x_2759_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2752_);
                    return v___y_2754_;
                }
            }
            24 => {
                if crate::leanh::lean_obj_tag(v___y_2767_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2767_, 1);
                    v___x_2768_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2769_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2770_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2771_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2766_);
                    v___x_2772_ = l_Lean_Parser_registerAlias(
                        v___x_2768_,
                        v___x_2769_,
                        v___x_2770_,
                        v___x_2771_,
                        v___y_2766_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2772_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2772_, 1);
                        v___x_2773_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2774_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2768_, v___x_2773_);
                        if crate::leanh::lean_obj_tag(v___x_2774_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2774_, 1);
                            v___x_2775_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2776_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2768_,
                                v___x_2775_,
                            );
                            v___y_2752_ = v___y_2766_;
                            v___y_2753_ = v___y_2765_;
                            v___y_2754_ = v___x_2776_;
                            state = 23;
                            continue;
                        } else {
                            v___y_2752_ = v___y_2766_;
                            v___y_2753_ = v___y_2765_;
                            v___y_2754_ = v___x_2774_;
                            state = 23;
                            continue;
                        }
                    } else {
                        v___y_2752_ = v___y_2766_;
                        v___y_2753_ = v___y_2765_;
                        v___y_2754_ = v___x_2772_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2766_);
                    return v___y_2767_;
                }
            }
            25 => {
                if crate::leanh::lean_obj_tag(v___y_2780_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2780_, 1);
                    v___x_2781_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2782_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2784_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2779_);
                    v___x_2785_ = l_Lean_Parser_registerAlias(
                        v___x_2781_,
                        v___x_2782_,
                        v___x_2783_,
                        v___x_2784_,
                        v___y_2779_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2785_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2785_, 1);
                        v___x_2786_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2787_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2781_, v___x_2786_);
                        if crate::leanh::lean_obj_tag(v___x_2787_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2787_, 1);
                            v___x_2788_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2789_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2781_,
                                v___x_2788_,
                            );
                            v___y_2765_ = v___y_2778_;
                            v___y_2766_ = v___y_2779_;
                            v___y_2767_ = v___x_2789_;
                            state = 24;
                            continue;
                        } else {
                            v___y_2765_ = v___y_2778_;
                            v___y_2766_ = v___y_2779_;
                            v___y_2767_ = v___x_2787_;
                            state = 24;
                            continue;
                        }
                    } else {
                        v___y_2765_ = v___y_2778_;
                        v___y_2766_ = v___y_2779_;
                        v___y_2767_ = v___x_2785_;
                        state = 24;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2779_);
                    return v___y_2780_;
                }
            }
            26 => {
                if crate::leanh::lean_obj_tag(v___y_2793_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2793_, 1);
                    v___x_2794_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2795_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2796_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2797_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2792_);
                    v___x_2798_ = l_Lean_Parser_registerAlias(
                        v___x_2794_,
                        v___x_2795_,
                        v___x_2796_,
                        v___x_2797_,
                        v___y_2792_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2798_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2798_, 1);
                        v___x_2799_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2800_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2794_, v___x_2799_);
                        if crate::leanh::lean_obj_tag(v___x_2800_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2800_, 1);
                            v___x_2801_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2802_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2794_,
                                v___x_2801_,
                            );
                            v___y_2778_ = v___y_2791_;
                            v___y_2779_ = v___y_2792_;
                            v___y_2780_ = v___x_2802_;
                            state = 25;
                            continue;
                        } else {
                            v___y_2778_ = v___y_2791_;
                            v___y_2779_ = v___y_2792_;
                            v___y_2780_ = v___x_2800_;
                            state = 25;
                            continue;
                        }
                    } else {
                        v___y_2778_ = v___y_2791_;
                        v___y_2779_ = v___y_2792_;
                        v___y_2780_ = v___x_2798_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2792_);
                    return v___y_2793_;
                }
            }
            27 => {
                if crate::leanh::lean_obj_tag(v___y_2806_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2806_, 1);
                    v___x_2807_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2808_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2810_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    crate::leanh::lean_inc_ref(v___y_2805_);
                    v___x_2811_ = l_Lean_Parser_registerAlias(
                        v___x_2807_,
                        v___x_2808_,
                        v___x_2809_,
                        v___x_2810_,
                        v___y_2805_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2811_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2811_, 1);
                        v___x_2812_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2813_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2807_, v___x_2812_);
                        if crate::leanh::lean_obj_tag(v___x_2813_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2813_, 1);
                            v___x_2814_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2815_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2807_,
                                v___x_2814_,
                            );
                            v___y_2791_ = v___y_2804_;
                            v___y_2792_ = v___y_2805_;
                            v___y_2793_ = v___x_2815_;
                            state = 26;
                            continue;
                        } else {
                            v___y_2791_ = v___y_2804_;
                            v___y_2792_ = v___y_2805_;
                            v___y_2793_ = v___x_2813_;
                            state = 26;
                            continue;
                        }
                    } else {
                        v___y_2791_ = v___y_2804_;
                        v___y_2792_ = v___y_2805_;
                        v___y_2793_ = v___x_2811_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2805_);
                    return v___y_2806_;
                }
            }
            28 => {
                if crate::leanh::lean_obj_tag(v___y_2817_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2817_, 1);
                    v___x_2818_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2819_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2820_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2821_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2822_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2823_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2824_ = l_Lean_Parser_registerAlias(
                        v___x_2818_,
                        v___x_2819_,
                        v___x_2820_,
                        v___x_2821_,
                        v___x_2823_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2824_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2824_, 1);
                        v___x_2825_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2826_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2818_, v___x_2825_);
                        if crate::leanh::lean_obj_tag(v___x_2826_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2826_, 1);
                            v___x_2827_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                            v___x_2828_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2818_,
                                v___x_2827_,
                            );
                            v___y_2804_ = v___x_2822_;
                            v___y_2805_ = v___x_2823_;
                            v___y_2806_ = v___x_2828_;
                            state = 27;
                            continue;
                        } else {
                            v___y_2804_ = v___x_2822_;
                            v___y_2805_ = v___x_2823_;
                            v___y_2806_ = v___x_2826_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v___y_2804_ = v___x_2822_;
                        v___y_2805_ = v___x_2823_;
                        v___y_2806_ = v___x_2824_;
                        state = 27;
                        continue;
                    }
                } else {
                    return v___y_2817_;
                }
            }
            29 => {
                if crate::leanh::lean_obj_tag(v___y_2830_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2830_, 1);
                    v___x_2831_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2832_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2833_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2834_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2835_ = l_Lean_Parser_registerAlias(
                        v___x_2831_,
                        v___x_2832_,
                        v___x_2833_,
                        v___x_2834_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2835_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2835_, 1);
                        v___x_2836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2837_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2831_, v___x_2836_);
                        if crate::leanh::lean_obj_tag(v___x_2837_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2837_, 1);
                            v___x_2838_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2839_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2831_,
                                v___x_2838_,
                            );
                            v___y_2817_ = v___x_2839_;
                            state = 28;
                            continue;
                        } else {
                            v___y_2817_ = v___x_2837_;
                            state = 28;
                            continue;
                        }
                    } else {
                        v___y_2817_ = v___x_2835_;
                        state = 28;
                        continue;
                    }
                } else {
                    return v___y_2830_;
                }
            }
            30 => {
                if crate::leanh::lean_obj_tag(v___y_2841_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_2841_, 1);
                    v___x_2842_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2843_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2844_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2845_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2846_ = l_Lean_Parser_registerAlias(
                        v___x_2842_,
                        v___x_2843_,
                        v___x_2844_,
                        v___x_2845_,
                        v___x_2659_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2846_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2846_, 1);
                        v___x_2847_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2848_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2842_, v___x_2847_);
                        if crate::leanh::lean_obj_tag(v___x_2848_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2848_, 1);
                            v___x_2849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                            v___x_2850_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_2842_,
                                v___x_2849_,
                            );
                            v___y_2830_ = v___x_2850_;
                            state = 29;
                            continue;
                        } else {
                            v___y_2830_ = v___x_2848_;
                            state = 29;
                            continue;
                        }
                    } else {
                        v___y_2830_ = v___x_2846_;
                        state = 29;
                        continue;
                    }
                } else {
                    return v___y_2841_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v_a_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2857_ = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
    return v_res_2857_;
}
pub unsafe fn lean_mk_antiquot_parenthesizer(
    mut v_name_2858_: *mut crate::leanh::LeanObject,
    mut v_kind_2859_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2860_: u8,
    mut v_isPseudoKind_2861_: u8,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2867_ = l_Lean_Parser_mkAntiquot_parenthesizer(
        v_name_2858_,
        v_kind_2859_,
        v_anonymous_2860_,
        v_isPseudoKind_2861_,
        v_a_2862_,
        v_a_2863_,
        v_a_2864_,
        v_a_2865_,
    );
    crate::leanh::lean_dec(v_a_2865_);
    crate::leanh::lean_dec_ref(v_a_2864_);
    crate::leanh::lean_dec(v_a_2863_);
    crate::leanh::lean_dec_ref(v_a_2862_);
    return v___x_2867_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(
    mut v_name_2868_: *mut crate::leanh::LeanObject,
    mut v_kind_2869_: *mut crate::leanh::LeanObject,
    mut v_anonymous_2870_: *mut crate::leanh::LeanObject,
    mut v_isPseudoKind_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
    mut v_a_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_2877_: u8 = 0;
    let mut v_isPseudoKind_boxed_2878_: u8 = 0;
    let mut v_res_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2877_ = (crate::leanh::lean_unbox(v_anonymous_2870_) as u8);
    v_isPseudoKind_boxed_2878_ = (crate::leanh::lean_unbox(v_isPseudoKind_2871_) as u8);
    v_res_2879_ = lean_mk_antiquot_parenthesizer(
        v_name_2868_,
        v_kind_2869_,
        v_anonymous_boxed_2877_,
        v_isPseudoKind_boxed_2878_,
        v_a_2872_,
        v_a_2873_,
        v_a_2874_,
        v_a_2875_,
    );
    return v_res_2879_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(
    mut v_a_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ =
        l_Lean_Parser_Term_ident_parenthesizer(v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
    return v___x_2885_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___boxed(
    mut v_a_2886_: *mut crate::leanh::LeanObject,
    mut v_a_2887_: *mut crate::leanh::LeanObject,
    mut v_a_2888_: *mut crate::leanh::LeanObject,
    mut v_a_2889_: *mut crate::leanh::LeanObject,
    mut v_a_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(
        v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_,
    );
    crate::leanh::lean_dec(v_a_2889_);
    crate::leanh::lean_dec_ref(v_a_2888_);
    crate::leanh::lean_dec(v_a_2887_);
    crate::leanh::lean_dec_ref(v_a_2886_);
    return v_res_2891_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2903_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0;
    v___x_2904_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2905_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2906_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4;
    v___x_2907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2904_,
        v___x_2905_,
        v___x_2906_,
        v___f_2903_,
    );
    return v___x_2907_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___boxed(
    mut v_a_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
    return v_res_2909_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Parser_Term_num_parenthesizer(v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
    return v___x_2915_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___boxed(
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_a_2917_: *mut crate::leanh::LeanObject,
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(
        v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_,
    );
    crate::leanh::lean_dec(v_a_2919_);
    crate::leanh::lean_dec_ref(v_a_2918_);
    crate::leanh::lean_dec(v_a_2917_);
    crate::leanh::lean_dec_ref(v_a_2916_);
    return v_res_2921_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2930_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0;
    v___x_2931_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2932_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2933_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1;
    v___x_2934_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2931_,
        v___x_2932_,
        v___x_2933_,
        v___f_2930_,
    );
    return v___x_2934_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___boxed(
    mut v_a_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2936_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
    return v_res_2936_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(
    mut v_a_2937_: *mut crate::leanh::LeanObject,
    mut v_a_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
    mut v_a_2940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2942_ =
        l_Lean_Parser_Term_scientific_parenthesizer(v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
    return v___x_2942_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___boxed(
    mut v_a_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(
        v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_,
    );
    crate::leanh::lean_dec(v_a_2946_);
    crate::leanh::lean_dec_ref(v_a_2945_);
    crate::leanh::lean_dec(v_a_2944_);
    crate::leanh::lean_dec_ref(v_a_2943_);
    return v_res_2948_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2957_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0;
    v___x_2958_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2959_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2960_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1;
    v___x_2961_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2958_,
        v___x_2959_,
        v___x_2960_,
        v___f_2957_,
    );
    return v___x_2961_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___boxed(
    mut v_a_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2963_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
    return v_res_2963_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Lean_Parser_Term_char_parenthesizer(v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
    return v___x_2969_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___boxed(
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(
        v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
    );
    crate::leanh::lean_dec(v_a_2973_);
    crate::leanh::lean_dec_ref(v_a_2972_);
    crate::leanh::lean_dec(v_a_2971_);
    crate::leanh::lean_dec_ref(v_a_2970_);
    return v_res_2975_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2984_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0;
    v___x_2985_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2986_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2987_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1;
    v___x_2988_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2985_,
        v___x_2986_,
        v___x_2987_,
        v___f_2984_,
    );
    return v___x_2988_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___boxed(
    mut v_a_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2990_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
    return v_res_2990_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(
    mut v_a_2991_: *mut crate::leanh::LeanObject,
    mut v_a_2992_: *mut crate::leanh::LeanObject,
    mut v_a_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2996_ = l_Lean_Parser_Term_str_parenthesizer(v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
    return v___x_2996_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___boxed(
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_a_3001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3002_ = l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(
        v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
    );
    crate::leanh::lean_dec(v_a_3000_);
    crate::leanh::lean_dec_ref(v_a_2999_);
    crate::leanh::lean_dec(v_a_2998_);
    crate::leanh::lean_dec_ref(v_a_2997_);
    return v_res_3002_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3011_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0;
    v___x_3012_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3013_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3014_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1;
    v___x_3015_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3012_,
        v___x_3013_,
        v___x_3014_,
        v___f_3011_,
    );
    return v___x_3015_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___boxed(
    mut v_a_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3017_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
    return v_res_3017_;
}
pub unsafe fn lean_pretty_printer_parenthesizer_interpret_parser_descr(
    mut v_x_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_a_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v_ref_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_name_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3069_: u8 = 0;
    let mut v_a_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v_ref_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3084_: u8 = 0;
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_name_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_a_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v_ref_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_kind_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_kind_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v_val_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_val_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_includeIdent_3154_: u8 = 0;
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_catName_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rbp_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_p_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sep_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3187_: u8 = 0;
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_p_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sep_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3204_: u8 = 0;
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_val_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asciiVal_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preserveForPP_3220_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3018_) {
                0 => {
                    crate::leanh::lean_dec(v_a_3020_);
                    v_name_3022_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    v_isSharedCheck_3051_ = (!crate::leanh::lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v___x_3024_ = v_x_3018_;
                        v_isShared_3025_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_name_3022_);
                        crate::leanh::lean_dec(v_x_3018_);
                        v___x_3024_ = crate::leanh::lean_box(0);
                        v_isShared_3025_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_name_3052_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    v_p_3053_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    v_isSharedCheck_3085_ = (!crate::leanh::lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3085_ == 0 {
                        v___x_3055_ = v_x_3018_;
                        v_isShared_3056_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_3053_);
                        crate::leanh::lean_inc(v_name_3052_);
                        crate::leanh::lean_dec(v_x_3018_);
                        v___x_3055_ = crate::leanh::lean_box(0);
                        v_isShared_3056_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_name_3086_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc(v_name_3086_);
                    v_p_u2081_3087_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc_ref(v_p_u2081_3087_);
                    v_p_u2082_3088_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc_ref(v_p_u2082_3088_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3089_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
                    v___x_3090_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_3089_, v_name_3086_);
                    if crate::leanh::lean_obj_tag(v___x_3090_) == 0 {
                        v_a_3091_ = crate::leanh::lean_ctor_get(v___x_3090_, 0);
                        crate::leanh::lean_inc(v_a_3091_);
                        crate::leanh::lean_dec_ref_known(v___x_3090_, 1);
                        crate::leanh::lean_inc(v_a_3020_);
                        crate::leanh::lean_inc_ref(v_a_3019_);
                        v___x_3092_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_p_u2081_3087_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3092_) == 0 {
                            v_a_3093_ = crate::leanh::lean_ctor_get(v___x_3092_, 0);
                            crate::leanh::lean_inc(v_a_3093_);
                            crate::leanh::lean_dec_ref_known(v___x_3092_, 1);
                            v___x_3094_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                                v_p_u2082_3088_,
                                v_a_3019_,
                                v_a_3020_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3094_) == 0 {
                                v_a_3095_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
                                v_isSharedCheck_3103_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3094_)) as u8;
                                if v_isSharedCheck_3103_ == 0 {
                                    v___x_3097_ = v___x_3094_;
                                    v_isShared_3098_ = v_isSharedCheck_3103_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3095_);
                                    crate::leanh::lean_dec(v___x_3094_);
                                    v___x_3097_ = crate::leanh::lean_box(0);
                                    v_isShared_3098_ = v_isSharedCheck_3103_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3093_);
                                crate::leanh::lean_dec(v_a_3091_);
                                return v___x_3094_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3091_);
                            crate::leanh::lean_dec_ref(v_p_u2082_3088_);
                            crate::leanh::lean_dec(v_a_3020_);
                            crate::leanh::lean_dec_ref(v_a_3019_);
                            return v___x_3092_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_u2082_3088_);
                        crate::leanh::lean_dec_ref(v_p_u2081_3087_);
                        crate::leanh::lean_dec(v_a_3020_);
                        v_a_3104_ = crate::leanh::lean_ctor_get(v___x_3090_, 0);
                        v_isSharedCheck_3116_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3090_)) as u8;
                        if v_isSharedCheck_3116_ == 0 {
                            v___x_3106_ = v___x_3090_;
                            v_isShared_3107_ = v_isSharedCheck_3116_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3104_);
                            crate::leanh::lean_dec(v___x_3090_);
                            v___x_3106_ = crate::leanh::lean_box(0);
                            v_isShared_3107_ = v_isSharedCheck_3116_;
                            state = 15;
                            continue;
                        }
                    }
                }
                3 => {
                    v_kind_3117_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc(v_kind_3117_);
                    v_prec_3118_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc(v_prec_3118_);
                    v_p_3119_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc_ref(v_p_3119_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3120_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3119_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3120_) == 0 {
                        v_a_3121_ = crate::leanh::lean_ctor_get(v___x_3120_, 0);
                        v_isSharedCheck_3129_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3120_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v___x_3123_ = v___x_3120_;
                            v_isShared_3124_ = v_isSharedCheck_3129_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3121_);
                            crate::leanh::lean_dec(v___x_3120_);
                            v___x_3123_ = crate::leanh::lean_box(0);
                            v_isShared_3124_ = v_isSharedCheck_3129_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_prec_3118_);
                        crate::leanh::lean_dec(v_kind_3117_);
                        return v___x_3120_;
                    }
                }
                4 => {
                    v_kind_3130_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc(v_kind_3130_);
                    v_prec_3131_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc(v_prec_3131_);
                    v_lhsPrec_3132_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc(v_lhsPrec_3132_);
                    v_p_3133_ = crate::leanh::lean_ctor_get(v_x_3018_, 3);
                    crate::leanh::lean_inc_ref(v_p_3133_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 4);
                    v___x_3134_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3133_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3134_) == 0 {
                        v_a_3135_ = crate::leanh::lean_ctor_get(v___x_3134_, 0);
                        v_isSharedCheck_3143_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3134_)) as u8;
                        if v_isSharedCheck_3143_ == 0 {
                            v___x_3137_ = v___x_3134_;
                            v_isShared_3138_ = v_isSharedCheck_3143_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3135_);
                            crate::leanh::lean_dec(v___x_3134_);
                            v___x_3137_ = crate::leanh::lean_box(0);
                            v_isShared_3138_ = v_isSharedCheck_3143_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_lhsPrec_3132_);
                        crate::leanh::lean_dec(v_prec_3131_);
                        crate::leanh::lean_dec(v_kind_3130_);
                        return v___x_3134_;
                    }
                }
                5 => {
                    crate::leanh::lean_dec(v_a_3020_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    v_val_3144_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    v_isSharedCheck_3152_ = (!crate::leanh::lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3152_ == 0 {
                        v___x_3146_ = v_x_3018_;
                        v_isShared_3147_ = v_isSharedCheck_3152_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3144_);
                        crate::leanh::lean_dec(v_x_3018_);
                        v___x_3146_ = crate::leanh::lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3152_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    crate::leanh::lean_dec(v_a_3020_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    v_val_3153_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc_ref(v_val_3153_);
                    v_includeIdent_3154_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 1);
                    v___x_3155_ = crate::leanh::lean_box((v_includeIdent_3154_) as usize);
                    v___x_3156_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3156_, 0, v_val_3153_);
                    crate::leanh::lean_closure_set(v___x_3156_, 1, v___x_3155_);
                    v___x_3157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                    return v___x_3157_;
                }
                7 => {
                    crate::leanh::lean_dec(v_a_3020_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    v_catName_3158_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc(v_catName_3158_);
                    v_rbp_3159_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc(v_rbp_3159_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 2);
                    v___x_3160_ = crate::leanh::lean_alloc_closure(
                        l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3160_, 0, v_catName_3158_);
                    crate::leanh::lean_closure_set(v___x_3160_, 1, v_rbp_3159_);
                    v___x_3161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3161_, 0, v___x_3160_);
                    return v___x_3161_;
                }
                8 => {
                    v_declName_3162_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc(v_declName_3162_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 1);
                    v___x_3163_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
                    v___x_3164_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
                        v___x_3163_,
                        v_declName_3162_,
                        v_a_3019_,
                        v_a_3020_,
                    );
                    crate::leanh::lean_dec(v_a_3020_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    return v___x_3164_;
                }
                9 => {
                    v_name_3165_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc_ref(v_name_3165_);
                    v_kind_3166_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc(v_kind_3166_);
                    v_p_3167_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc_ref(v_p_3167_);
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3168_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3167_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3168_) == 0 {
                        v_a_3169_ = crate::leanh::lean_ctor_get(v___x_3168_, 0);
                        v_isSharedCheck_3183_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3168_)) as u8;
                        if v_isSharedCheck_3183_ == 0 {
                            v___x_3171_ = v___x_3168_;
                            v_isShared_3172_ = v_isSharedCheck_3183_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3169_);
                            crate::leanh::lean_dec(v___x_3168_);
                            v___x_3171_ = crate::leanh::lean_box(0);
                            v_isShared_3172_ = v_isSharedCheck_3183_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_kind_3166_);
                        crate::leanh::lean_dec_ref(v_name_3165_);
                        return v___x_3168_;
                    }
                }
                10 => {
                    v_p_3184_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc_ref(v_p_3184_);
                    v_sep_3185_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc_ref(v_sep_3185_);
                    v_psep_3186_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc_ref(v_psep_3186_);
                    v_allowTrailingSep_3187_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 3);
                    crate::leanh::lean_inc(v_a_3020_);
                    crate::leanh::lean_inc_ref(v_a_3019_);
                    v___x_3188_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3184_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3188_) == 0 {
                        v_a_3189_ = crate::leanh::lean_ctor_get(v___x_3188_, 0);
                        crate::leanh::lean_inc(v_a_3189_);
                        crate::leanh::lean_dec_ref_known(v___x_3188_, 1);
                        v___x_3190_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_psep_3186_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3190_) == 0 {
                            v_a_3191_ = crate::leanh::lean_ctor_get(v___x_3190_, 0);
                            v_isSharedCheck_3200_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3190_)) as u8;
                            if v_isSharedCheck_3200_ == 0 {
                                v___x_3193_ = v___x_3190_;
                                v_isShared_3194_ = v_isSharedCheck_3200_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3191_);
                                crate::leanh::lean_dec(v___x_3190_);
                                v___x_3193_ = crate::leanh::lean_box(0);
                                v_isShared_3194_ = v_isSharedCheck_3200_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3189_);
                            crate::leanh::lean_dec_ref(v_sep_3185_);
                            return v___x_3190_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_psep_3186_);
                        crate::leanh::lean_dec_ref(v_sep_3185_);
                        crate::leanh::lean_dec(v_a_3020_);
                        crate::leanh::lean_dec_ref(v_a_3019_);
                        return v___x_3188_;
                    }
                }
                11 => {
                    v_p_3201_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc_ref(v_p_3201_);
                    v_sep_3202_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc_ref(v_sep_3202_);
                    v_psep_3203_ = crate::leanh::lean_ctor_get(v_x_3018_, 2);
                    crate::leanh::lean_inc_ref(v_psep_3203_);
                    v_allowTrailingSep_3204_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 3);
                    crate::leanh::lean_inc(v_a_3020_);
                    crate::leanh::lean_inc_ref(v_a_3019_);
                    v___x_3205_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3201_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3205_) == 0 {
                        v_a_3206_ = crate::leanh::lean_ctor_get(v___x_3205_, 0);
                        crate::leanh::lean_inc(v_a_3206_);
                        crate::leanh::lean_dec_ref_known(v___x_3205_, 1);
                        v___x_3207_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_psep_3203_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3207_) == 0 {
                            v_a_3208_ = crate::leanh::lean_ctor_get(v___x_3207_, 0);
                            v_isSharedCheck_3217_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3207_)) as u8;
                            if v_isSharedCheck_3217_ == 0 {
                                v___x_3210_ = v___x_3207_;
                                v_isShared_3211_ = v_isSharedCheck_3217_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3208_);
                                crate::leanh::lean_dec(v___x_3207_);
                                v___x_3210_ = crate::leanh::lean_box(0);
                                v_isShared_3211_ = v_isSharedCheck_3217_;
                                state = 27;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3206_);
                            crate::leanh::lean_dec_ref(v_sep_3202_);
                            return v___x_3207_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_psep_3203_);
                        crate::leanh::lean_dec_ref(v_sep_3202_);
                        crate::leanh::lean_dec(v_a_3020_);
                        crate::leanh::lean_dec_ref(v_a_3019_);
                        return v___x_3205_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_a_3020_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    v_val_3218_ = crate::leanh::lean_ctor_get(v_x_3018_, 0);
                    crate::leanh::lean_inc_ref(v_val_3218_);
                    v_asciiVal_3219_ = crate::leanh::lean_ctor_get(v_x_3018_, 1);
                    crate::leanh::lean_inc_ref(v_asciiVal_3219_);
                    v_preserveForPP_3220_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3018_, 2);
                    v___x_3221_ = crate::leanh::lean_box((v_preserveForPP_3220_) as usize);
                    v___x_3222_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Parser_unicodeSymbol_parenthesizer___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_3222_, 0, v_val_3218_);
                    crate::leanh::lean_closure_set(v___x_3222_, 1, v_asciiVal_3219_);
                    crate::leanh::lean_closure_set(v___x_3222_, 2, v___x_3221_);
                    v___x_3223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3223_, 0, v___x_3222_);
                    return v___x_3223_;
                }
            },
            1 => {
                v___x_3026_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
                v___x_3027_ = l_Lean_Parser_getConstAlias___redArg(v___x_3026_, v_name_3022_);
                if crate::leanh::lean_obj_tag(v___x_3027_) == 0 {
                    crate::leanh::lean_del_object(v___x_3024_);
                    crate::leanh::lean_dec_ref(v_a_3019_);
                    v_a_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3035_ = (!crate::leanh::lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v___x_3030_ = v___x_3027_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3028_);
                        crate::leanh::lean_dec(v___x_3027_);
                        v___x_3030_ = crate::leanh::lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3036_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3050_ = (!crate::leanh::lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3038_ = v___x_3027_;
                        v_isShared_3039_ = v_isSharedCheck_3050_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3036_);
                        crate::leanh::lean_dec(v___x_3027_);
                        v___x_3038_ = crate::leanh::lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3050_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3031_ == 0 {
                    v___x_3033_ = v___x_3030_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3033_;
            }
            4 => {
                v_ref_3040_ = crate::leanh::lean_ctor_get(v_a_3019_, 5);
                crate::leanh::lean_inc(v_ref_3040_);
                crate::leanh::lean_dec_ref(v_a_3019_);
                v___x_3041_ = lean_io_error_to_string(v_a_3036_);
                if v_isShared_3025_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3024_, 3);
                    crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3041_);
                    v___x_3043_ = v___x_3024_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3041_);
                    v___x_3043_ = v_reuseFailAlloc_3049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3044_ = l_Lean_MessageData_ofFormat(v___x_3043_);
                v___x_3045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3045_, 0, v_ref_3040_);
                crate::leanh::lean_ctor_set(v___x_3045_, 1, v___x_3044_);
                if v_isShared_3039_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3038_, 0, v___x_3045_);
                    v___x_3047_ = v___x_3038_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
                    v___x_3047_ = v_reuseFailAlloc_3048_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3047_;
            }
            7 => {
                v___x_3057_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
                v___x_3058_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_3057_, v_name_3052_);
                if crate::leanh::lean_obj_tag(v___x_3058_) == 0 {
                    crate::leanh::lean_del_object(v___x_3055_);
                    v_a_3059_ = crate::leanh::lean_ctor_get(v___x_3058_, 0);
                    crate::leanh::lean_inc(v_a_3059_);
                    crate::leanh::lean_dec_ref_known(v___x_3058_, 1);
                    v___x_3060_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3053_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3060_) == 0 {
                        v_a_3061_ = crate::leanh::lean_ctor_get(v___x_3060_, 0);
                        v_isSharedCheck_3069_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3060_)) as u8;
                        if v_isSharedCheck_3069_ == 0 {
                            v___x_3063_ = v___x_3060_;
                            v_isShared_3064_ = v_isSharedCheck_3069_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3061_);
                            crate::leanh::lean_dec(v___x_3060_);
                            v___x_3063_ = crate::leanh::lean_box(0);
                            v_isShared_3064_ = v_isSharedCheck_3069_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3059_);
                        return v___x_3060_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_3053_);
                    crate::leanh::lean_dec(v_a_3020_);
                    v_a_3070_ = crate::leanh::lean_ctor_get(v___x_3058_, 0);
                    v_isSharedCheck_3084_ = (!crate::leanh::lean_is_exclusive(v___x_3058_)) as u8;
                    if v_isSharedCheck_3084_ == 0 {
                        v___x_3072_ = v___x_3058_;
                        v_isShared_3073_ = v_isSharedCheck_3084_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3070_);
                        crate::leanh::lean_dec(v___x_3058_);
                        v___x_3072_ = crate::leanh::lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3084_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3065_ = crate::leanh::lean_apply_1(v_a_3059_, v_a_3061_);
                if v_isShared_3064_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3063_, 0, v___x_3065_);
                    v___x_3067_ = v___x_3063_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
                    v___x_3067_ = v_reuseFailAlloc_3068_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3067_;
            }
            10 => {
                v_ref_3074_ = crate::leanh::lean_ctor_get(v_a_3019_, 5);
                crate::leanh::lean_inc(v_ref_3074_);
                crate::leanh::lean_dec_ref(v_a_3019_);
                v___x_3075_ = lean_io_error_to_string(v_a_3070_);
                v___x_3076_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3076_, 0, v___x_3075_);
                v___x_3077_ = l_Lean_MessageData_ofFormat(v___x_3076_);
                if v_isShared_3056_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3055_, 0);
                    crate::leanh::lean_ctor_set(v___x_3055_, 1, v___x_3077_);
                    crate::leanh::lean_ctor_set(v___x_3055_, 0, v_ref_3074_);
                    v___x_3079_ = v___x_3055_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_ref_3074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3077_);
                    v___x_3079_ = v_reuseFailAlloc_3083_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3072_, 0, v___x_3079_);
                    v___x_3081_ = v___x_3072_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3081_;
            }
            13 => {
                v___x_3099_ = crate::leanh::lean_apply_2(v_a_3091_, v_a_3093_, v_a_3095_);
                if v_isShared_3098_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3097_, 0, v___x_3099_);
                    v___x_3101_ = v___x_3097_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
                    v___x_3101_ = v_reuseFailAlloc_3102_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3101_;
            }
            15 => {
                v_ref_3108_ = crate::leanh::lean_ctor_get(v_a_3019_, 5);
                crate::leanh::lean_inc(v_ref_3108_);
                crate::leanh::lean_dec_ref(v_a_3019_);
                v___x_3109_ = lean_io_error_to_string(v_a_3104_);
                v___x_3110_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                v___x_3111_ = l_Lean_MessageData_ofFormat(v___x_3110_);
                v___x_3112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3112_, 0, v_ref_3108_);
                crate::leanh::lean_ctor_set(v___x_3112_, 1, v___x_3111_);
                if v_isShared_3107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3106_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3106_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3114_;
            }
            17 => {
                v___x_3125_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    8,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_3125_, 0, v_kind_3117_);
                crate::leanh::lean_closure_set(v___x_3125_, 1, v_prec_3118_);
                crate::leanh::lean_closure_set(v___x_3125_, 2, v_a_3121_);
                if v_isShared_3124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3123_, 0, v___x_3125_);
                    v___x_3127_ = v___x_3123_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3127_;
            }
            19 => {
                v___x_3139_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3139_, 0, v_kind_3130_);
                crate::leanh::lean_closure_set(v___x_3139_, 1, v_prec_3131_);
                crate::leanh::lean_closure_set(v___x_3139_, 2, v_lhsPrec_3132_);
                crate::leanh::lean_closure_set(v___x_3139_, 3, v_a_3135_);
                if v_isShared_3138_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3137_, 0, v___x_3139_);
                    v___x_3141_ = v___x_3137_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3141_;
            }
            21 => {
                v___x_3148_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_symbol_parenthesizer___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3148_, 0, v_val_3144_);
                if v_isShared_3147_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3146_, 0);
                    crate::leanh::lean_ctor_set(v___x_3146_, 0, v___x_3148_);
                    v___x_3150_ = v___x_3146_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
                    v___x_3150_ = v_reuseFailAlloc_3151_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3150_;
            }
            23 => {
                v___x_3173_ = 1;
                v___x_3174_ = 0;
                v___x_3175_ = crate::leanh::lean_box((v___x_3173_) as usize);
                v___x_3176_ = crate::leanh::lean_box((v___x_3174_) as usize);
                crate::leanh::lean_inc(v_kind_3166_);
                v___x_3177_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3177_, 0, v_name_3165_);
                crate::leanh::lean_closure_set(v___x_3177_, 1, v_kind_3166_);
                crate::leanh::lean_closure_set(v___x_3177_, 2, v___x_3175_);
                crate::leanh::lean_closure_set(v___x_3177_, 3, v___x_3176_);
                v___x_3178_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3178_, 0, v_kind_3166_);
                crate::leanh::lean_closure_set(v___x_3178_, 1, v_a_3169_);
                v___x_3179_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3179_, 0, v___x_3177_);
                crate::leanh::lean_closure_set(v___x_3179_, 1, v___x_3178_);
                if v_isShared_3172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3171_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3171_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3181_;
            }
            25 => {
                v___x_3195_ = crate::leanh::lean_box((v_allowTrailingSep_3187_) as usize);
                v___x_3196_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_sepBy_parenthesizer___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3196_, 0, v_a_3189_);
                crate::leanh::lean_closure_set(v___x_3196_, 1, v_sep_3185_);
                crate::leanh::lean_closure_set(v___x_3196_, 2, v_a_3191_);
                crate::leanh::lean_closure_set(v___x_3196_, 3, v___x_3195_);
                if v_isShared_3194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3193_, 0, v___x_3196_);
                    v___x_3198_ = v___x_3193_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3198_;
            }
            27 => {
                v___x_3212_ = crate::leanh::lean_box((v_allowTrailingSep_3204_) as usize);
                v___x_3213_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_sepBy1_parenthesizer___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3213_, 0, v_a_3206_);
                crate::leanh::lean_closure_set(v___x_3213_, 1, v_sep_3202_);
                crate::leanh::lean_closure_set(v___x_3213_, 2, v_a_3208_);
                crate::leanh::lean_closure_set(v___x_3213_, 3, v___x_3212_);
                if v_isShared_3211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3210_, 0, v___x_3213_);
                    v___x_3215_ = v___x_3210_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
                    v___x_3215_ = v_reuseFailAlloc_3216_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_interpretParserDescr___boxed(
    mut v_x_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3228_ =
        lean_pretty_printer_parenthesizer_interpret_parser_descr(v_x_3224_, v_a_3225_, v_a_3226_);
    return v_res_3228_;
}
pub unsafe fn lean_mk_antiquot_formatter(
    mut v_name_3229_: *mut crate::leanh::LeanObject,
    mut v_kind_3230_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3231_: u8,
    mut v_isPseudoKind_3232_: u8,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3238_ = l_Lean_Parser_mkAntiquot_formatter(
        v_name_3229_,
        v_kind_3230_,
        v_anonymous_3231_,
        v_isPseudoKind_3232_,
        v_a_3233_,
        v_a_3234_,
        v_a_3235_,
        v_a_3236_,
    );
    crate::leanh::lean_dec(v_a_3236_);
    crate::leanh::lean_dec_ref(v_a_3235_);
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    return v___x_3238_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(
    mut v_name_3239_: *mut crate::leanh::LeanObject,
    mut v_kind_3240_: *mut crate::leanh::LeanObject,
    mut v_anonymous_3241_: *mut crate::leanh::LeanObject,
    mut v_isPseudoKind_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_anonymous_boxed_3248_: u8 = 0;
    let mut v_isPseudoKind_boxed_3249_: u8 = 0;
    let mut v_res_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3248_ = (crate::leanh::lean_unbox(v_anonymous_3241_) as u8);
    v_isPseudoKind_boxed_3249_ = (crate::leanh::lean_unbox(v_isPseudoKind_3242_) as u8);
    v_res_3250_ = lean_mk_antiquot_formatter(
        v_name_3239_,
        v_kind_3240_,
        v_anonymous_boxed_3248_,
        v_isPseudoKind_boxed_3249_,
        v_a_3243_,
        v_a_3244_,
        v_a_3245_,
        v_a_3246_,
    );
    return v_res_3250_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_ident_formatter(
    mut v_a_3251_: *mut crate::leanh::LeanObject,
    mut v_a_3252_: *mut crate::leanh::LeanObject,
    mut v_a_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Parser_Term_ident_formatter(v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_ident_formatter___boxed(
    mut v_a_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ =
        l_Lean_PrettyPrinter_Formatter_ident_formatter(v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
    crate::leanh::lean_dec(v_a_3260_);
    crate::leanh::lean_dec_ref(v_a_3259_);
    crate::leanh::lean_dec(v_a_3258_);
    crate::leanh::lean_dec_ref(v_a_3257_);
    return v_res_3262_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3273_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0;
    v___x_3274_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3275_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3276_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3;
    v___x_3277_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3274_,
        v___x_3275_,
        v___x_3276_,
        v___f_3273_,
    );
    return v___x_3277_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___boxed(
    mut v_a_3278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3279_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
    return v_res_3279_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_numLit_formatter(
    mut v_a_3280_: *mut crate::leanh::LeanObject,
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_Parser_Term_num_formatter(v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_numLit_formatter___boxed(
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3291_ =
        l_Lean_PrettyPrinter_Formatter_numLit_formatter(v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
    crate::leanh::lean_dec(v_a_3289_);
    crate::leanh::lean_dec_ref(v_a_3288_);
    crate::leanh::lean_dec(v_a_3287_);
    crate::leanh::lean_dec_ref(v_a_3286_);
    return v_res_3291_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3300_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0;
    v___x_3301_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3302_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3303_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1;
    v___x_3304_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3301_,
        v___x_3302_,
        v___x_3303_,
        v___f_3300_,
    );
    return v___x_3304_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___boxed(
    mut v_a_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
    return v_res_3306_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ =
        l_Lean_Parser_Term_scientific_formatter(v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
    return v___x_3312_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_scientificLit_formatter___boxed(
    mut v_a_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3318_ = l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(
        v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_,
    );
    crate::leanh::lean_dec(v_a_3316_);
    crate::leanh::lean_dec_ref(v_a_3315_);
    crate::leanh::lean_dec(v_a_3314_);
    crate::leanh::lean_dec_ref(v_a_3313_);
    return v_res_3318_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3327_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0;
    v___x_3328_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3329_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3330_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1;
    v___x_3331_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3328_,
        v___x_3329_,
        v___x_3330_,
        v___f_3327_,
    );
    return v___x_3331_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___boxed(
    mut v_a_3332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3333_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
    return v_res_3333_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_charLit_formatter(
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Parser_Term_char_formatter(v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_charLit_formatter___boxed(
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3345_ = l_Lean_PrettyPrinter_Formatter_charLit_formatter(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_,
    );
    crate::leanh::lean_dec(v_a_3343_);
    crate::leanh::lean_dec_ref(v_a_3342_);
    crate::leanh::lean_dec(v_a_3341_);
    crate::leanh::lean_dec_ref(v_a_3340_);
    return v_res_3345_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3354_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0;
    v___x_3355_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3356_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3357_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1;
    v___x_3358_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3355_,
        v___x_3356_,
        v___x_3357_,
        v___f_3354_,
    );
    return v___x_3358_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___boxed(
    mut v_a_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
    return v_res_3360_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_strLit_formatter(
    mut v_a_3361_: *mut crate::leanh::LeanObject,
    mut v_a_3362_: *mut crate::leanh::LeanObject,
    mut v_a_3363_: *mut crate::leanh::LeanObject,
    mut v_a_3364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_Parser_Term_str_formatter(v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
    return v___x_3366_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_strLit_formatter___boxed(
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ =
        l_Lean_PrettyPrinter_Formatter_strLit_formatter(v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
    crate::leanh::lean_dec(v_a_3370_);
    crate::leanh::lean_dec_ref(v_a_3369_);
    crate::leanh::lean_dec(v_a_3368_);
    crate::leanh::lean_dec_ref(v_a_3367_);
    return v_res_3372_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3381_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0;
    v___x_3382_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3383_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_3384_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1;
    v___x_3385_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3382_,
        v___x_3383_,
        v___x_3384_,
        v___f_3381_,
    );
    return v___x_3385_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___boxed(
    mut v_a_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3387_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
    return v_res_3387_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(
    mut v___x_3388_: *mut crate::leanh::LeanObject,
    mut v___x_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3395_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3388_,
        v___x_3389_,
        v___y_3390_,
        v___y_3391_,
        v___y_3392_,
        v___y_3393_,
    );
    return v___x_3395_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed(
    mut v___x_3396_: *mut crate::leanh::LeanObject,
    mut v___x_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(
        v___x_3396_,
        v___x_3397_,
        v___y_3398_,
        v___y_3399_,
        v___y_3400_,
        v___y_3401_,
    );
    crate::leanh::lean_dec(v___y_3401_);
    crate::leanh::lean_dec_ref(v___y_3400_);
    crate::leanh::lean_dec(v___y_3399_);
    crate::leanh::lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn lean_pretty_printer_formatter_interpret_parser_descr(
    mut v_x_3404_: *mut crate::leanh::LeanObject,
    mut v_a_3405_: *mut crate::leanh::LeanObject,
    mut v_a_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3421_: u8 = 0;
    let mut v_a_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v_ref_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_name_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v_ref_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_name_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut v_a_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v_ref_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v_kind_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3514_: u8 = 0;
    let mut v_kind_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_val_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_val_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_catName_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut v_p_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sep_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_p_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sep_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_psep_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3588_: u8 = 0;
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v_val_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asciiVal_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preserveForPP_3604_: u8 = 0;
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3404_) {
                0 => {
                    crate::leanh::lean_dec(v_a_3406_);
                    v_name_3408_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3437_ = (!crate::leanh::lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3437_ == 0 {
                        v___x_3410_ = v_x_3404_;
                        v_isShared_3411_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_name_3408_);
                        crate::leanh::lean_dec(v_x_3404_);
                        v___x_3410_ = crate::leanh::lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_name_3438_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    v_p_3439_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    v_isSharedCheck_3471_ = (!crate::leanh::lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3471_ == 0 {
                        v___x_3441_ = v_x_3404_;
                        v_isShared_3442_ = v_isSharedCheck_3471_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_3439_);
                        crate::leanh::lean_inc(v_name_3438_);
                        crate::leanh::lean_dec(v_x_3404_);
                        v___x_3441_ = crate::leanh::lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3471_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_name_3472_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc(v_name_3472_);
                    v_p_u2081_3473_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc_ref(v_p_u2081_3473_);
                    v_p_u2082_3474_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc_ref(v_p_u2082_3474_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3475_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
                    v___x_3476_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_3475_, v_name_3472_);
                    if crate::leanh::lean_obj_tag(v___x_3476_) == 0 {
                        v_a_3477_ = crate::leanh::lean_ctor_get(v___x_3476_, 0);
                        crate::leanh::lean_inc(v_a_3477_);
                        crate::leanh::lean_dec_ref_known(v___x_3476_, 1);
                        crate::leanh::lean_inc(v_a_3406_);
                        crate::leanh::lean_inc_ref(v_a_3405_);
                        v___x_3478_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_p_u2081_3473_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3478_, 0);
                            crate::leanh::lean_inc(v_a_3479_);
                            crate::leanh::lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = lean_pretty_printer_formatter_interpret_parser_descr(
                                v_p_u2082_3474_,
                                v_a_3405_,
                                v_a_3406_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3480_) == 0 {
                                v_a_3481_ = crate::leanh::lean_ctor_get(v___x_3480_, 0);
                                v_isSharedCheck_3489_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3480_)) as u8;
                                if v_isSharedCheck_3489_ == 0 {
                                    v___x_3483_ = v___x_3480_;
                                    v_isShared_3484_ = v_isSharedCheck_3489_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3481_);
                                    crate::leanh::lean_dec(v___x_3480_);
                                    v___x_3483_ = crate::leanh::lean_box(0);
                                    v_isShared_3484_ = v_isSharedCheck_3489_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3479_);
                                crate::leanh::lean_dec(v_a_3477_);
                                return v___x_3480_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3477_);
                            crate::leanh::lean_dec_ref(v_p_u2082_3474_);
                            crate::leanh::lean_dec(v_a_3406_);
                            crate::leanh::lean_dec_ref(v_a_3405_);
                            return v___x_3478_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_u2082_3474_);
                        crate::leanh::lean_dec_ref(v_p_u2081_3473_);
                        crate::leanh::lean_dec(v_a_3406_);
                        v_a_3490_ = crate::leanh::lean_ctor_get(v___x_3476_, 0);
                        v_isSharedCheck_3502_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3476_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v___x_3492_ = v___x_3476_;
                            v_isShared_3493_ = v_isSharedCheck_3502_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3490_);
                            crate::leanh::lean_dec(v___x_3476_);
                            v___x_3492_ = crate::leanh::lean_box(0);
                            v_isShared_3493_ = v_isSharedCheck_3502_;
                            state = 15;
                            continue;
                        }
                    }
                }
                3 => {
                    v_kind_3503_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc(v_kind_3503_);
                    v_p_3504_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc_ref(v_p_3504_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3505_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3504_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3505_) == 0 {
                        v_a_3506_ = crate::leanh::lean_ctor_get(v___x_3505_, 0);
                        v_isSharedCheck_3514_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3505_)) as u8;
                        if v_isSharedCheck_3514_ == 0 {
                            v___x_3508_ = v___x_3505_;
                            v_isShared_3509_ = v_isSharedCheck_3514_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3506_);
                            crate::leanh::lean_dec(v___x_3505_);
                            v___x_3508_ = crate::leanh::lean_box(0);
                            v_isShared_3509_ = v_isSharedCheck_3514_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_kind_3503_);
                        return v___x_3505_;
                    }
                }
                4 => {
                    v_kind_3515_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc(v_kind_3515_);
                    v_prec_3516_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc(v_prec_3516_);
                    v_lhsPrec_3517_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc(v_lhsPrec_3517_);
                    v_p_3518_ = crate::leanh::lean_ctor_get(v_x_3404_, 3);
                    crate::leanh::lean_inc_ref(v_p_3518_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 4);
                    v___x_3519_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3518_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3519_) == 0 {
                        v_a_3520_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                        v_isSharedCheck_3528_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                        if v_isSharedCheck_3528_ == 0 {
                            v___x_3522_ = v___x_3519_;
                            v_isShared_3523_ = v_isSharedCheck_3528_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3520_);
                            crate::leanh::lean_dec(v___x_3519_);
                            v___x_3522_ = crate::leanh::lean_box(0);
                            v_isShared_3523_ = v_isSharedCheck_3528_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_lhsPrec_3517_);
                        crate::leanh::lean_dec(v_prec_3516_);
                        crate::leanh::lean_dec(v_kind_3515_);
                        return v___x_3519_;
                    }
                }
                5 => {
                    crate::leanh::lean_dec(v_a_3406_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    v_val_3529_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3537_ = (!crate::leanh::lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3537_ == 0 {
                        v___x_3531_ = v_x_3404_;
                        v_isShared_3532_ = v_isSharedCheck_3537_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3529_);
                        crate::leanh::lean_dec(v_x_3404_);
                        v___x_3531_ = crate::leanh::lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3537_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    crate::leanh::lean_dec(v_a_3406_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    v_val_3538_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc_ref(v_val_3538_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 1);
                    v___x_3539_ = 0;
                    v___x_3540_ = crate::leanh::lean_box((v___x_3539_) as usize);
                    v___x_3541_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Parser_nonReservedSymbol_formatter___boxed as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_3541_, 0, v_val_3538_);
                    crate::leanh::lean_closure_set(v___x_3541_, 1, v___x_3540_);
                    v___x_3542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3542_, 0, v___x_3541_);
                    return v___x_3542_;
                }
                7 => {
                    crate::leanh::lean_dec(v_a_3406_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    v_catName_3543_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc(v_catName_3543_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 2);
                    v___x_3544_ = crate::leanh::lean_alloc_closure(
                        l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_3544_, 0, v_catName_3543_);
                    v___x_3545_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3545_, 0, v___x_3544_);
                    return v___x_3545_;
                }
                8 => {
                    v_declName_3546_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc(v_declName_3546_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 1);
                    v___x_3547_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
                    v___x_3548_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
                        v___x_3547_,
                        v_declName_3546_,
                        v_a_3405_,
                        v_a_3406_,
                    );
                    crate::leanh::lean_dec(v_a_3406_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    return v___x_3548_;
                }
                9 => {
                    v_name_3549_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc_ref(v_name_3549_);
                    v_kind_3550_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc(v_kind_3550_);
                    v_p_3551_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc_ref(v_p_3551_);
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3552_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3551_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3552_) == 0 {
                        v_a_3553_ = crate::leanh::lean_ctor_get(v___x_3552_, 0);
                        v_isSharedCheck_3567_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3552_)) as u8;
                        if v_isSharedCheck_3567_ == 0 {
                            v___x_3555_ = v___x_3552_;
                            v_isShared_3556_ = v_isSharedCheck_3567_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3553_);
                            crate::leanh::lean_dec(v___x_3552_);
                            v___x_3555_ = crate::leanh::lean_box(0);
                            v_isShared_3556_ = v_isSharedCheck_3567_;
                            state = 23;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_kind_3550_);
                        crate::leanh::lean_dec_ref(v_name_3549_);
                        return v___x_3552_;
                    }
                }
                10 => {
                    v_p_3568_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc_ref(v_p_3568_);
                    v_sep_3569_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc_ref(v_sep_3569_);
                    v_psep_3570_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc_ref(v_psep_3570_);
                    v_allowTrailingSep_3571_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 3);
                    crate::leanh::lean_inc(v_a_3406_);
                    crate::leanh::lean_inc_ref(v_a_3405_);
                    v___x_3572_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3568_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3572_) == 0 {
                        v_a_3573_ = crate::leanh::lean_ctor_get(v___x_3572_, 0);
                        crate::leanh::lean_inc(v_a_3573_);
                        crate::leanh::lean_dec_ref_known(v___x_3572_, 1);
                        v___x_3574_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_psep_3570_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3574_) == 0 {
                            v_a_3575_ = crate::leanh::lean_ctor_get(v___x_3574_, 0);
                            v_isSharedCheck_3584_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3574_)) as u8;
                            if v_isSharedCheck_3584_ == 0 {
                                v___x_3577_ = v___x_3574_;
                                v_isShared_3578_ = v_isSharedCheck_3584_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3575_);
                                crate::leanh::lean_dec(v___x_3574_);
                                v___x_3577_ = crate::leanh::lean_box(0);
                                v_isShared_3578_ = v_isSharedCheck_3584_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3573_);
                            crate::leanh::lean_dec_ref(v_sep_3569_);
                            return v___x_3574_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_psep_3570_);
                        crate::leanh::lean_dec_ref(v_sep_3569_);
                        crate::leanh::lean_dec(v_a_3406_);
                        crate::leanh::lean_dec_ref(v_a_3405_);
                        return v___x_3572_;
                    }
                }
                11 => {
                    v_p_3585_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc_ref(v_p_3585_);
                    v_sep_3586_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc_ref(v_sep_3586_);
                    v_psep_3587_ = crate::leanh::lean_ctor_get(v_x_3404_, 2);
                    crate::leanh::lean_inc_ref(v_psep_3587_);
                    v_allowTrailingSep_3588_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 3);
                    crate::leanh::lean_inc(v_a_3406_);
                    crate::leanh::lean_inc_ref(v_a_3405_);
                    v___x_3589_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3585_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3589_) == 0 {
                        v_a_3590_ = crate::leanh::lean_ctor_get(v___x_3589_, 0);
                        crate::leanh::lean_inc(v_a_3590_);
                        crate::leanh::lean_dec_ref_known(v___x_3589_, 1);
                        v___x_3591_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_psep_3587_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3591_) == 0 {
                            v_a_3592_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                            v_isSharedCheck_3601_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3591_)) as u8;
                            if v_isSharedCheck_3601_ == 0 {
                                v___x_3594_ = v___x_3591_;
                                v_isShared_3595_ = v_isSharedCheck_3601_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3592_);
                                crate::leanh::lean_dec(v___x_3591_);
                                v___x_3594_ = crate::leanh::lean_box(0);
                                v_isShared_3595_ = v_isSharedCheck_3601_;
                                state = 27;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3590_);
                            crate::leanh::lean_dec_ref(v_sep_3586_);
                            return v___x_3591_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_psep_3587_);
                        crate::leanh::lean_dec_ref(v_sep_3586_);
                        crate::leanh::lean_dec(v_a_3406_);
                        crate::leanh::lean_dec_ref(v_a_3405_);
                        return v___x_3589_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_a_3406_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    v_val_3602_ = crate::leanh::lean_ctor_get(v_x_3404_, 0);
                    crate::leanh::lean_inc_ref(v_val_3602_);
                    v_asciiVal_3603_ = crate::leanh::lean_ctor_get(v_x_3404_, 1);
                    crate::leanh::lean_inc_ref(v_asciiVal_3603_);
                    v_preserveForPP_3604_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_3404_, 2);
                    v___x_3605_ = crate::leanh::lean_box((v_preserveForPP_3604_) as usize);
                    v___x_3606_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Parser_unicodeSymbol_formatter___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_3606_, 0, v_val_3602_);
                    crate::leanh::lean_closure_set(v___x_3606_, 1, v_asciiVal_3603_);
                    crate::leanh::lean_closure_set(v___x_3606_, 2, v___x_3605_);
                    v___x_3607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3607_, 0, v___x_3606_);
                    return v___x_3607_;
                }
            },
            1 => {
                v___x_3412_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
                v___x_3413_ = l_Lean_Parser_getConstAlias___redArg(v___x_3412_, v_name_3408_);
                if crate::leanh::lean_obj_tag(v___x_3413_) == 0 {
                    crate::leanh::lean_del_object(v___x_3410_);
                    crate::leanh::lean_dec_ref(v_a_3405_);
                    v_a_3414_ = crate::leanh::lean_ctor_get(v___x_3413_, 0);
                    v_isSharedCheck_3421_ = (!crate::leanh::lean_is_exclusive(v___x_3413_)) as u8;
                    if v_isSharedCheck_3421_ == 0 {
                        v___x_3416_ = v___x_3413_;
                        v_isShared_3417_ = v_isSharedCheck_3421_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3414_);
                        crate::leanh::lean_dec(v___x_3413_);
                        v___x_3416_ = crate::leanh::lean_box(0);
                        v_isShared_3417_ = v_isSharedCheck_3421_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3422_ = crate::leanh::lean_ctor_get(v___x_3413_, 0);
                    v_isSharedCheck_3436_ = (!crate::leanh::lean_is_exclusive(v___x_3413_)) as u8;
                    if v_isSharedCheck_3436_ == 0 {
                        v___x_3424_ = v___x_3413_;
                        v_isShared_3425_ = v_isSharedCheck_3436_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3422_);
                        crate::leanh::lean_dec(v___x_3413_);
                        v___x_3424_ = crate::leanh::lean_box(0);
                        v_isShared_3425_ = v_isSharedCheck_3436_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3417_ == 0 {
                    v___x_3419_ = v___x_3416_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
                    v___x_3419_ = v_reuseFailAlloc_3420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3419_;
            }
            4 => {
                v_ref_3426_ = crate::leanh::lean_ctor_get(v_a_3405_, 5);
                crate::leanh::lean_inc(v_ref_3426_);
                crate::leanh::lean_dec_ref(v_a_3405_);
                v___x_3427_ = lean_io_error_to_string(v_a_3422_);
                if v_isShared_3411_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3410_, 3);
                    crate::leanh::lean_ctor_set(v___x_3410_, 0, v___x_3427_);
                    v___x_3429_ = v___x_3410_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3427_);
                    v___x_3429_ = v_reuseFailAlloc_3435_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3430_ = l_Lean_MessageData_ofFormat(v___x_3429_);
                v___x_3431_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3431_, 0, v_ref_3426_);
                crate::leanh::lean_ctor_set(v___x_3431_, 1, v___x_3430_);
                if v_isShared_3425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3424_, 0, v___x_3431_);
                    v___x_3433_ = v___x_3424_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
                    v___x_3433_ = v_reuseFailAlloc_3434_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3433_;
            }
            7 => {
                v___x_3443_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
                v___x_3444_ = l_Lean_Parser_getUnaryAlias___redArg(v___x_3443_, v_name_3438_);
                if crate::leanh::lean_obj_tag(v___x_3444_) == 0 {
                    crate::leanh::lean_del_object(v___x_3441_);
                    v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                    crate::leanh::lean_inc(v_a_3445_);
                    crate::leanh::lean_dec_ref_known(v___x_3444_, 1);
                    v___x_3446_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3439_, v_a_3405_, v_a_3406_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3446_) == 0 {
                        v_a_3447_ = crate::leanh::lean_ctor_get(v___x_3446_, 0);
                        v_isSharedCheck_3455_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3446_)) as u8;
                        if v_isSharedCheck_3455_ == 0 {
                            v___x_3449_ = v___x_3446_;
                            v_isShared_3450_ = v_isSharedCheck_3455_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3447_);
                            crate::leanh::lean_dec(v___x_3446_);
                            v___x_3449_ = crate::leanh::lean_box(0);
                            v_isShared_3450_ = v_isSharedCheck_3455_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3445_);
                        return v___x_3446_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_3439_);
                    crate::leanh::lean_dec(v_a_3406_);
                    v_a_3456_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                    v_isSharedCheck_3470_ = (!crate::leanh::lean_is_exclusive(v___x_3444_)) as u8;
                    if v_isSharedCheck_3470_ == 0 {
                        v___x_3458_ = v___x_3444_;
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3456_);
                        crate::leanh::lean_dec(v___x_3444_);
                        v___x_3458_ = crate::leanh::lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3451_ = crate::leanh::lean_apply_1(v_a_3445_, v_a_3447_);
                if v_isShared_3450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3449_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3449_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3453_;
            }
            10 => {
                v_ref_3460_ = crate::leanh::lean_ctor_get(v_a_3405_, 5);
                crate::leanh::lean_inc(v_ref_3460_);
                crate::leanh::lean_dec_ref(v_a_3405_);
                v___x_3461_ = lean_io_error_to_string(v_a_3456_);
                v___x_3462_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3462_, 0, v___x_3461_);
                v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
                if v_isShared_3442_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3441_, 0);
                    crate::leanh::lean_ctor_set(v___x_3441_, 1, v___x_3463_);
                    crate::leanh::lean_ctor_set(v___x_3441_, 0, v_ref_3460_);
                    v___x_3465_ = v___x_3441_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_ref_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3463_);
                    v___x_3465_ = v_reuseFailAlloc_3469_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3459_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3458_, 0, v___x_3465_);
                    v___x_3467_ = v___x_3458_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3467_;
            }
            13 => {
                v___x_3485_ = crate::leanh::lean_apply_2(v_a_3477_, v_a_3479_, v_a_3481_);
                if v_isShared_3484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3483_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3483_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3487_;
            }
            15 => {
                v_ref_3494_ = crate::leanh::lean_ctor_get(v_a_3405_, 5);
                crate::leanh::lean_inc(v_ref_3494_);
                crate::leanh::lean_dec_ref(v_a_3405_);
                v___x_3495_ = lean_io_error_to_string(v_a_3490_);
                v___x_3496_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3496_, 0, v___x_3495_);
                v___x_3497_ = l_Lean_MessageData_ofFormat(v___x_3496_);
                v___x_3498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3498_, 0, v_ref_3494_);
                crate::leanh::lean_ctor_set(v___x_3498_, 1, v___x_3497_);
                if v_isShared_3493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3498_);
                    v___x_3500_ = v___x_3492_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3500_;
            }
            17 => {
                v___x_3510_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3510_, 0, v_kind_3503_);
                crate::leanh::lean_closure_set(v___x_3510_, 1, v_a_3506_);
                if v_isShared_3509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3510_);
                    v___x_3512_ = v___x_3508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
                    v___x_3512_ = v_reuseFailAlloc_3513_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3512_;
            }
            19 => {
                v___x_3524_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3524_, 0, v_kind_3515_);
                crate::leanh::lean_closure_set(v___x_3524_, 1, v_prec_3516_);
                crate::leanh::lean_closure_set(v___x_3524_, 2, v_lhsPrec_3517_);
                crate::leanh::lean_closure_set(v___x_3524_, 3, v_a_3520_);
                if v_isShared_3523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3522_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3526_;
            }
            21 => {
                v___x_3533_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_symbol_formatter___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_3533_, 0, v_val_3529_);
                if v_isShared_3532_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3531_, 0);
                    crate::leanh::lean_ctor_set(v___x_3531_, 0, v___x_3533_);
                    v___x_3535_ = v___x_3531_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
                    v___x_3535_ = v_reuseFailAlloc_3536_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3535_;
            }
            23 => {
                v___x_3557_ = 1;
                v___x_3558_ = 0;
                v___x_3559_ = crate::leanh::lean_box((v___x_3557_) as usize);
                v___x_3560_ = crate::leanh::lean_box((v___x_3558_) as usize);
                crate::leanh::lean_inc(v_kind_3550_);
                v___x_3561_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3561_, 0, v_name_3549_);
                crate::leanh::lean_closure_set(v___x_3561_, 1, v_kind_3550_);
                crate::leanh::lean_closure_set(v___x_3561_, 2, v___x_3559_);
                crate::leanh::lean_closure_set(v___x_3561_, 3, v___x_3560_);
                v___x_3562_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3562_, 0, v_kind_3550_);
                crate::leanh::lean_closure_set(v___x_3562_, 1, v_a_3553_);
                v___f_3563_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3563_, 0, v___x_3561_);
                crate::leanh::lean_closure_set(v___f_3563_, 1, v___x_3562_);
                if v_isShared_3556_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3555_, 0, v___f_3563_);
                    v___x_3565_ = v___x_3555_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___f_3563_);
                    v___x_3565_ = v_reuseFailAlloc_3566_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3565_;
            }
            25 => {
                v___x_3579_ = crate::leanh::lean_box((v_allowTrailingSep_3571_) as usize);
                v___x_3580_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_sepBy_formatter___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3580_, 0, v_a_3573_);
                crate::leanh::lean_closure_set(v___x_3580_, 1, v_sep_3569_);
                crate::leanh::lean_closure_set(v___x_3580_, 2, v_a_3575_);
                crate::leanh::lean_closure_set(v___x_3580_, 3, v___x_3579_);
                if v_isShared_3578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3577_, 0, v___x_3580_);
                    v___x_3582_ = v___x_3577_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3582_;
            }
            27 => {
                v___x_3596_ = crate::leanh::lean_box((v_allowTrailingSep_3588_) as usize);
                v___x_3597_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Parser_sepBy1_formatter___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___x_3597_, 0, v_a_3590_);
                crate::leanh::lean_closure_set(v___x_3597_, 1, v_sep_3586_);
                crate::leanh::lean_closure_set(v___x_3597_, 2, v_a_3592_);
                crate::leanh::lean_closure_set(v___x_3597_, 3, v___x_3596_);
                if v_isShared_3595_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3594_, 0, v___x_3597_);
                    v___x_3599_ = v___x_3594_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_interpretParserDescr___boxed(
    mut v_x_3608_: *mut crate::leanh::LeanObject,
    mut v_a_3609_: *mut crate::leanh::LeanObject,
    mut v_a_3610_: *mut crate::leanh::LeanObject,
    mut v_a_3611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ =
        lean_pretty_printer_formatter_interpret_parser_descr(v_x_3608_, v_a_3609_, v_a_3610_);
    return v_res_3612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser(builtin);
}
