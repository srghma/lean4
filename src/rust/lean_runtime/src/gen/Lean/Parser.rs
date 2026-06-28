// Lean compiler output
// Module: Lean.Parser
// Imports: Lean.Parser.Basic Lean.Parser.Level Lean.Parser.Term Lean.Parser.Tactic Lean.Parser.Command Lean.Parser.Module Lean.Parser.Syntax Lean.Parser.Do Lean.Parser.Tactic.Doc
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr5};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
};
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 114, 114, 101, 108, 101, 118, 97, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [119, 115, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17759471530397124190 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 111, 116, 70, 111, 108, 108, 111, 119, 101, 100, 66, 121, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,5889158377769613190 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8201135813669748762 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 99, 111, 118, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11451883528579887567 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2510058869824260539 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_recover as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [97, 110, 100, 116, 104, 101, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12571085391447129896 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,10645341263474320100 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_andthen as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__32_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__33_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__35_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__36_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 114, 101, 108, 115, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,393173242845875278 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__37_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,3598234189925664274 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_orelse as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__40_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__43_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__45_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__46_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [104, 101, 120, 110, 117, 109, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11510626477845773464 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__47_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11982095303264823988 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__53_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,18163029821153688220 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__54_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2797157559945049776 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_interpolatedStr as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__57_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__59_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,14298422259736409839 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__60_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_interpolatedStr_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__62_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_interpolatedStr_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__64_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__65_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [119, 105, 116, 104, 111, 117, 116, 70, 111, 114, 98, 105, 100, 100, 101, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2488176001515375140 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__66_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,15810495650029311976 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__69_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__72_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutForbidden_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__74_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__75_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 105, 116, 104, 111, 117, 116, 80, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1164644006045091397 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__76_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17508920231745936945 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__79_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__82_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withoutPosition_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__84_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__85_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [119, 105, 116, 104, 80, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17180264478054591478 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__86_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,5944786210894363754 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withPosition as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__89_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_withPosition_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__92_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__94_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__95_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 104, 101, 99, 107, 87, 115, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__96_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,14787378393065436163 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 112, 97, 99, 101, 32, 98, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 112, 116, 105, 111, 110, 97, 108, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,18170484695678750185 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__102_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2933775029743101773 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__105_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__108_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__110_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__111_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 110, 121, 49, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,16727513630015613089 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__112_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12455907124956747413 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1Indent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__117_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1Indent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__119_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__120_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 110, 121, 73, 110, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12240491195871077271 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__121_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1556038599081871155 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_manyIndent_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__126_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_manyIndent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__128_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__129_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 110, 121, 49, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17243740965612849207 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__130_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,13889654070509321555 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__133_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__136_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many1_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__138_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__139_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 97, 110, 121, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2302572775315350313 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__140_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11576560798023578125 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__143_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__146_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__148_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__149_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 116, 111, 109, 105, 99, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,4024150434455327032 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__151_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__150_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11052958945290096852 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_atomic as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__153_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__154_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__152_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__155_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__156_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_atomic_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__157_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__159_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 111, 111, 107, 97, 104, 101, 97, 100, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,3382831200566926872 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__162_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__161_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,15235553684503663412 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_lookahead as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__164_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__165_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__163_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__166_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_lookahead_formatter___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__167_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_lookahead_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__169_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__170_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 101, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__171_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,7429455657892634123 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 104, 101, 99, 107, 76, 105, 110, 101, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,14251682899144180462 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__180_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,10019628956073368425 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 69, 113, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,304087650447937403 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 71, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__189_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,4942254933594350711 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 71, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,10876008678127703429 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 108, 71, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__198_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17597206043415342265 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 104, 101, 99, 107, 67, 111, 108, 71, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,17716280446251572173 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__207_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,3737801725909557423 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_hygieneInfo_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__212_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_hygieneInfo_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__214_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__215_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [114, 97, 119, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,930173994822296688 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__216_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11160707415378428636 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_rawIdent_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__220_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_rawIdent_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__222_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__223_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12357768255797326360 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_ident_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__229_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_ident_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__231_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__232_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__233_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12926801259741997275 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 99, 105, 101, 110, 116, 105, 102, 105, 99, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11460878236439353836 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_scientificLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__239_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_scientificLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__241_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__242_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__243_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,5949480926448383572 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 109, 101, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__245_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8815315524667565364 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_nameLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__249_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_nameLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__251_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__252_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 104, 97, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__253_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,16760301032635233067 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 104, 97, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11096140698252235337 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_charLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__259_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_charLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__261_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__262_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [115, 116, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__263_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,9232979286016572671 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,3202936226761841983 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_strLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__269_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_strLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__271_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__272_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__273_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,6110315075117401315 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 117, 109, 76, 105, 116, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,15973081547164711991 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__278_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__279_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__280_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_numLit_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__281_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_numLit_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__283_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__284_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 105, 110, 101, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__285_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,4800675059916378954 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 104, 101, 99, 107, 76, 105, 110, 101, 98, 114, 101, 97, 107, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__287_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,3297028327859390570 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 105, 110, 101, 32, 98, 114, 101, 97, 107, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 87, 115, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__295_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1581446985683836252 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [99, 104, 101, 99, 107, 78, 111, 87, 115, 66, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__297_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,8982410250343985142 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [110, 111, 32, 115, 112, 97, 99, 101, 32, 98, 101, 102, 111, 114, 101, 0]};
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_ident_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject,6375785142665761018 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,6741636008758929801 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject,738098606605637560 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_num_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject,6375785142665761018 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,6443958244076462206 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject,6861786668853825883 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_scientific_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject,6375785142665761018 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11724492440903985589 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject,18319288711560907444 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_char_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject,6375785142665761018 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,1945590011008718296 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject,3745412335828369085 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_str_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__2_value) as *mut LeanObject,6375785142665761018 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,12532102953669115254 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__3_value) as *mut LeanObject,929601914512300979 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_ident_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [70, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject,582838245365662195 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__224_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,10890885640717993884 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject,5191661447043754805 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_num_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject,582838245365662195 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__275_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,2835361733898899899 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject,12071238001331397246 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_scientific_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject,582838245365662195 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__235_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,7590009743772624840 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject,1377634676658237465 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_char_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject,582838245365662195 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__255_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,4774526234884175813 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject,745663875097992408 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Term_str_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1___closed__1_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__1_value) as *mut LeanObject,582838245365662195 as *mut LeanObject] };
static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__265_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__value) as *mut LeanObject,4708573442450243427 as *mut LeanObject] };
pub static l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1___closed__2_value) as *mut LeanObject,16580378683988055606 as *mut LeanObject] };
static mut l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    v___x_1812_ = l_Lean_PrettyPrinter_Formatter_resetLeadWord___redArg(v___y_1808_);
    return v___x_1812_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1818_: *mut LeanObject = core::ptr::null_mut();
    v_res_1818_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
    lean_dec(v___y_1816_);
    lean_dec_ref(v___y_1815_);
    lean_dec(v___y_1814_);
    lean_dec_ref(v___y_1813_);
    return v_res_1818_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = lean_apply_5(
        v___y_1819_,
        v___y_1820_,
        v___y_1821_,
        v___y_1822_,
        v___y_1823_,
        lean_box(0),
    );
    return v___x_1825_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1832_: *mut LeanObject = core::ptr::null_mut();
    v_res_1832_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
    return v_res_1832_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_1835_ = l_Lean_Parser_checkColGe(v___x_1834_);
    return v___x_1835_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1837_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_1838_ = l_Lean_Parser_andthen(v___x_1837_, v___y_1836_);
    v___x_1839_ = l_Lean_Parser_many(v___x_1838_);
    v___x_1840_ = l_Lean_Parser_withPosition(v___x_1839_);
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__3_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___lam__2___closed__1_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_1843_ = l_Lean_Parser_andthen(v___x_1842_, v___y_1841_);
    v___x_1844_ = l_Lean_Parser_many1(v___x_1843_);
    v___x_1845_ = l_Lean_Parser_withPosition(v___x_1844_);
    return v___x_1845_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lean_PrettyPrinter_Parenthesizer_visitToken___redArg(v___y_1847_);
    return v___x_1851_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__4_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_);
    lean_dec(v___y_1855_);
    lean_dec_ref(v___y_1854_);
    lean_dec(v___y_1853_);
    lean_dec_ref(v___y_1852_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ = lean_apply_5(
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
        v___y_1861_,
        v___y_1862_,
        lean_box(0),
    );
    return v___x_1864_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2____boxed(
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1871_: *mut LeanObject = core::ptr::null_mut();
    v_res_1871_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__6_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
    return v_res_1871_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_(
    mut v_x_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l___private_Lean_Parser_0__Lean_Parser_initFn___lam__5___closed__0_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_1875_ = l_Lean_Parser_notFollowedBy(v_x_1873_, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_Parser_hexnum;
    v___x_1963_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1963_, 0, v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    v___x_1966_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_hexnum_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1967_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    return v___x_1967_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__98_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2052_ = l_Lean_Parser_checkWsBefore(v___x_2051_);
    return v___x_2052_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    v___x_2053_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__99_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2054_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2054_, 0, v___x_2053_);
    return v___x_2054_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__173_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2197_ = l_Lean_Parser_checkLineEq(v___x_2196_);
    return v___x_2197_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v___x_2198_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__175_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2199_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2199_, 0, v___x_2198_);
    return v___x_2199_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    v___x_2202_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkLineEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2203_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2203_, 0, v___x_2202_);
    return v___x_2203_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v___x_2204_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLineEq_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2205_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2205_, 0, v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    v___x_2214_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__182_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2215_ = l_Lean_Parser_checkColEq(v___x_2214_);
    return v___x_2215_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    v___x_2216_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__184_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2217_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2217_, 0, v___x_2216_);
    return v___x_2217_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    v___x_2220_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColEq_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2221_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2221_, 0, v___x_2220_);
    return v___x_2221_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    v___x_2222_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColEq_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2223_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2223_, 0, v___x_2222_);
    return v___x_2223_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    v___x_2232_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__191_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2233_ = l_Lean_Parser_checkColGe(v___x_2232_);
    return v___x_2233_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__193_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2235_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2235_, 0, v___x_2234_);
    return v___x_2235_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGe_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    return v___x_2239_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    v___x_2240_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGe_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2241_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2241_, 0, v___x_2240_);
    return v___x_2241_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__200_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2251_ = l_Lean_Parser_checkColGt(v___x_2250_);
    return v___x_2251_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    v___x_2252_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__202_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2253_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2253_, 0, v___x_2252_);
    return v___x_2253_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    v___x_2256_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkColGt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2257_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2257_, 0, v___x_2256_);
    return v___x_2257_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2258_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkColGt_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2259_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2259_, 0, v___x_2258_);
    return v___x_2259_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    v___x_2267_ = l_Lean_Parser_hygieneInfo;
    v___x_2268_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2268_, 0, v___x_2267_);
    return v___x_2268_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    v___x_2284_ = l_Lean_Parser_rawIdent;
    v___x_2285_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2285_, 0, v___x_2284_);
    return v___x_2285_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    v___x_2299_ = l_Lean_Parser_ident;
    v___x_2300_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    return v___x_2300_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    v___x_2317_ = l_Lean_Parser_scientificLit;
    v___x_2318_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2318_, 0, v___x_2317_);
    return v___x_2318_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    v___x_2335_ = l_Lean_Parser_nameLit;
    v___x_2336_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2336_, 0, v___x_2335_);
    return v___x_2336_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    v___x_2353_ = l_Lean_Parser_charLit;
    v___x_2354_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    return v___x_2354_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_2371_ = l_Lean_Parser_strLit;
    v___x_2372_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2372_, 0, v___x_2371_);
    return v___x_2372_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    v___x_2389_ = l_Lean_Parser_numLit;
    v___x_2390_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    return v___x_2390_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__289_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2415_ = l_Lean_Parser_checkLinebreakBefore(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    v___x_2416_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__290_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2417_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2417_, 0, v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    v___x_2420_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkLinebreakBefore_formatter___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2421_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2421_, 0, v___x_2420_);
    return v___x_2421_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    v___x_2422_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkLinebreakBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2423_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2423_, 0, v___x_2422_);
    return v___x_2423_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2433_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__299_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
    v___x_2434_ = l_Lean_Parser_checkNoWsBefore(v___x_2433_);
    return v___x_2434_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    v___x_2435_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__300_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
    v___x_2436_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2436_, 0, v___x_2435_);
    return v___x_2436_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2441_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkNoWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2442_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2442_, 0, v___x_2441_);
    return v___x_2442_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    v___x_2443_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkWsBefore_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2444_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2444_, 0, v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    v___x_2445_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_checkWsBefore_parenthesizer___boxed
            as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2446_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2446_, 0, v___x_2445_);
    return v___x_2446_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2570_: u8 = 0;
    let mut v___y_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2586_: u8 = 0;
    let mut v___y_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2601_: u8 = 0;
    let mut v___y_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: u8 = 0;
    let mut v___y_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2631_: u8 = 0;
    let mut v___y_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2448_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2564_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__97_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__100_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                v___x_2566_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__101_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2567_ = lean_box(0);
                v___x_2659_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__160_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                v___x_2851_ = l_Lean_Parser_registerAlias(
                    v___x_2448_,
                    v___x_2564_,
                    v___x_2565_,
                    v___x_2566_,
                    v___x_2659_,
                );
                if lean_obj_tag(v___x_2851_) == 0 {
                    lean_dec_ref_known(v___x_2851_, 1);
                    v___x_2852_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__305_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2853_ =
                        l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2448_, v___x_2852_);
                    if lean_obj_tag(v___x_2853_) == 0 {
                        lean_dec_ref_known(v___x_2853_, 1);
                        v___x_2854_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__306_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                if lean_obj_tag(v___y_2451_) == 0 {
                    lean_dec_ref_known(v___y_2451_, 1);
                    v___x_2452_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2453_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2454_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2455_ = lean_box(0);
                    v___x_2456_ = l_Lean_Parser_registerAlias(
                        v___x_2452_,
                        v___x_2453_,
                        v___x_2454_,
                        v___x_2455_,
                        v___y_2450_,
                    );
                    if lean_obj_tag(v___x_2456_) == 0 {
                        lean_dec_ref_known(v___x_2456_, 1);
                        v___x_2457_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2458_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                            v___x_2452_,
                            v___x_2457_,
                        );
                        if lean_obj_tag(v___x_2458_) == 0 {
                            lean_dec_ref_known(v___x_2458_, 1);
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
                    lean_dec_ref(v___y_2450_);
                    return v___y_2451_;
                }
            }
            2 => {
                if lean_obj_tag(v___y_2463_) == 0 {
                    lean_dec_ref_known(v___y_2463_, 1);
                    v___x_2464_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2465_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2466_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2467_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2462_);
                    v___x_2468_ = l_Lean_Parser_registerAlias(
                        v___x_2464_,
                        v___x_2465_,
                        v___x_2466_,
                        v___x_2467_,
                        v___y_2462_,
                    );
                    if lean_obj_tag(v___x_2468_) == 0 {
                        lean_dec_ref_known(v___x_2468_, 1);
                        v___x_2469_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2470_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2464_, v___x_2469_);
                        if lean_obj_tag(v___x_2470_) == 0 {
                            lean_dec_ref_known(v___x_2470_, 1);
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
                    lean_dec_ref(v___y_2462_);
                    return v___y_2463_;
                }
            }
            3 => {
                if lean_obj_tag(v___y_2476_) == 0 {
                    lean_dec_ref_known(v___y_2476_, 1);
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
                    if lean_obj_tag(v___x_2481_) == 0 {
                        lean_dec_ref_known(v___x_2481_, 1);
                        v___x_2482_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__34_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2483_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2477_, v___x_2482_);
                        if lean_obj_tag(v___x_2483_) == 0 {
                            lean_dec_ref_known(v___x_2483_, 1);
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
                    lean_dec_ref(v___y_2475_);
                    lean_dec_ref(v___y_2474_);
                    return v___y_2476_;
                }
            }
            4 => {
                if lean_obj_tag(v___y_2489_) == 0 {
                    lean_dec_ref_known(v___y_2489_, 1);
                    v___x_2490_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__38_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2491_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__39_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2492_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__41_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2493_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__42_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2488_);
                    v___x_2494_ = l_Lean_Parser_registerAlias(
                        v___x_2490_,
                        v___x_2491_,
                        v___x_2492_,
                        v___x_2493_,
                        v___y_2488_,
                    );
                    if lean_obj_tag(v___x_2494_) == 0 {
                        lean_dec_ref_known(v___x_2494_, 1);
                        v___x_2495_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__44_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2496_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2490_, v___x_2495_);
                        if lean_obj_tag(v___x_2496_) == 0 {
                            lean_dec_ref_known(v___x_2496_, 1);
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
                    lean_dec_ref(v___y_2488_);
                    lean_dec_ref(v___y_2487_);
                    return v___y_2489_;
                }
            }
            5 => {
                if lean_obj_tag(v___y_2502_) == 0 {
                    lean_dec_ref_known(v___y_2502_, 1);
                    v___x_2503_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__48_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2504_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__49_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2505_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__50_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2506_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__51_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2501_);
                    v___x_2507_ = l_Lean_Parser_registerAlias(
                        v___x_2503_,
                        v___x_2504_,
                        v___x_2505_,
                        v___x_2506_,
                        v___y_2501_,
                    );
                    if lean_obj_tag(v___x_2507_) == 0 {
                        lean_dec_ref_known(v___x_2507_, 1);
                        v___x_2508_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__52_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2509_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2503_, v___x_2508_);
                        if lean_obj_tag(v___x_2509_) == 0 {
                            lean_dec_ref_known(v___x_2509_, 1);
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
                    lean_dec_ref(v___y_2501_);
                    lean_dec_ref(v___y_2500_);
                    return v___y_2502_;
                }
            }
            6 => {
                if lean_obj_tag(v___y_2515_) == 0 {
                    lean_dec_ref_known(v___y_2515_, 1);
                    v___x_2516_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__55_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2517_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__56_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2518_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__58_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2519_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__61_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2514_);
                    v___x_2520_ = l_Lean_Parser_registerAlias(
                        v___x_2516_,
                        v___x_2517_,
                        v___x_2518_,
                        v___x_2519_,
                        v___y_2514_,
                    );
                    if lean_obj_tag(v___x_2520_) == 0 {
                        lean_dec_ref_known(v___x_2520_, 1);
                        v___x_2521_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__63_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2522_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2516_, v___x_2521_);
                        if lean_obj_tag(v___x_2522_) == 0 {
                            lean_dec_ref_known(v___x_2522_, 1);
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
                    lean_dec_ref(v___y_2514_);
                    lean_dec_ref(v___y_2513_);
                    return v___y_2515_;
                }
            }
            7 => {
                if lean_obj_tag(v___y_2528_) == 0 {
                    lean_dec_ref_known(v___y_2528_, 1);
                    v___x_2529_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__67_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2530_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__68_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2531_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__70_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2532_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__71_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2526_);
                    v___x_2533_ = l_Lean_Parser_registerAlias(
                        v___x_2529_,
                        v___x_2530_,
                        v___x_2531_,
                        v___x_2532_,
                        v___y_2526_,
                    );
                    if lean_obj_tag(v___x_2533_) == 0 {
                        lean_dec_ref_known(v___x_2533_, 1);
                        v___x_2534_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__73_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2535_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2529_, v___x_2534_);
                        if lean_obj_tag(v___x_2535_) == 0 {
                            lean_dec_ref_known(v___x_2535_, 1);
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
                    lean_dec_ref(v___y_2527_);
                    lean_dec_ref(v___y_2526_);
                    return v___y_2528_;
                }
            }
            8 => {
                if lean_obj_tag(v___y_2541_) == 0 {
                    lean_dec_ref_known(v___y_2541_, 1);
                    v___x_2542_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__77_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2543_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__78_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2544_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__80_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2545_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__81_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2539_);
                    v___x_2546_ = l_Lean_Parser_registerAlias(
                        v___x_2542_,
                        v___x_2543_,
                        v___x_2544_,
                        v___x_2545_,
                        v___y_2539_,
                    );
                    if lean_obj_tag(v___x_2546_) == 0 {
                        lean_dec_ref_known(v___x_2546_, 1);
                        v___x_2547_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__83_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2548_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2542_, v___x_2547_);
                        if lean_obj_tag(v___x_2548_) == 0 {
                            lean_dec_ref_known(v___x_2548_, 1);
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
                    lean_dec_ref(v___y_2540_);
                    lean_dec_ref(v___y_2539_);
                    return v___y_2541_;
                }
            }
            9 => {
                if lean_obj_tag(v___y_2554_) == 0 {
                    lean_dec_ref_known(v___y_2554_, 1);
                    v___x_2555_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__87_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2556_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__88_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2557_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__90_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2558_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__91_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2552_);
                    v___x_2559_ = l_Lean_Parser_registerAlias(
                        v___x_2555_,
                        v___x_2556_,
                        v___x_2557_,
                        v___x_2558_,
                        v___y_2552_,
                    );
                    if lean_obj_tag(v___x_2559_) == 0 {
                        lean_dec_ref_known(v___x_2559_, 1);
                        v___x_2560_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__93_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2561_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2555_, v___x_2560_);
                        if lean_obj_tag(v___x_2561_) == 0 {
                            lean_dec_ref_known(v___x_2561_, 1);
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
                    lean_dec_ref(v___y_2553_);
                    lean_dec_ref(v___y_2552_);
                    return v___y_2554_;
                }
            }
            10 => {
                if lean_obj_tag(v___y_2573_) == 0 {
                    lean_dec_ref_known(v___y_2573_, 1);
                    v___x_2574_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__103_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2575_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__104_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2576_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__106_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2577_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__107_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc(v___y_2572_);
                    v___x_2578_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_2578_, 0, v___x_2567_);
                    lean_ctor_set(v___x_2578_, 1, v___y_2572_);
                    lean_ctor_set_uint8(
                        v___x_2578_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___y_2570_,
                    );
                    v___x_2579_ = l_Lean_Parser_registerAlias(
                        v___x_2574_,
                        v___x_2575_,
                        v___x_2576_,
                        v___x_2577_,
                        v___x_2578_,
                    );
                    if lean_obj_tag(v___x_2579_) == 0 {
                        lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2580_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__109_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2581_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2574_, v___x_2580_);
                        if lean_obj_tag(v___x_2581_) == 0 {
                            lean_dec_ref_known(v___x_2581_, 1);
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
                    lean_dec_ref(v___y_2571_);
                    lean_dec_ref(v___y_2569_);
                    return v___y_2573_;
                }
            }
            11 => {
                if lean_obj_tag(v___y_2589_) == 0 {
                    lean_dec_ref_known(v___y_2589_, 1);
                    v___x_2590_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__113_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2591_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__114_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2592_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__115_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2593_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__116_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2588_);
                    v___x_2594_ = l_Lean_Parser_registerAlias(
                        v___x_2590_,
                        v___x_2591_,
                        v___x_2592_,
                        v___x_2593_,
                        v___y_2588_,
                    );
                    if lean_obj_tag(v___x_2594_) == 0 {
                        lean_dec_ref_known(v___x_2594_, 1);
                        v___x_2595_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__118_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2596_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2590_, v___x_2595_);
                        if lean_obj_tag(v___x_2596_) == 0 {
                            lean_dec_ref_known(v___x_2596_, 1);
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
                    lean_dec_ref(v___y_2588_);
                    lean_dec_ref(v___y_2585_);
                    return v___y_2589_;
                }
            }
            12 => {
                if lean_obj_tag(v___y_2604_) == 0 {
                    lean_dec_ref_known(v___y_2604_, 1);
                    v___x_2605_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__122_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2606_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__123_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2607_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__124_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2608_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__125_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2603_);
                    v___x_2609_ = l_Lean_Parser_registerAlias(
                        v___x_2605_,
                        v___x_2606_,
                        v___x_2607_,
                        v___x_2608_,
                        v___y_2603_,
                    );
                    if lean_obj_tag(v___x_2609_) == 0 {
                        lean_dec_ref_known(v___x_2609_, 1);
                        v___x_2610_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__127_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2611_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2605_, v___x_2610_);
                        if lean_obj_tag(v___x_2611_) == 0 {
                            lean_dec_ref_known(v___x_2611_, 1);
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
                    lean_dec_ref(v___y_2603_);
                    lean_dec_ref(v___y_2600_);
                    return v___y_2604_;
                }
            }
            13 => {
                if lean_obj_tag(v___y_2619_) == 0 {
                    lean_dec_ref_known(v___y_2619_, 1);
                    v___x_2620_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__131_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2621_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__132_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2622_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__134_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2623_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__135_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2618_);
                    v___x_2624_ = l_Lean_Parser_registerAlias(
                        v___x_2620_,
                        v___x_2621_,
                        v___x_2622_,
                        v___x_2623_,
                        v___y_2618_,
                    );
                    if lean_obj_tag(v___x_2624_) == 0 {
                        lean_dec_ref_known(v___x_2624_, 1);
                        v___x_2625_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__137_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2626_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2620_, v___x_2625_);
                        if lean_obj_tag(v___x_2626_) == 0 {
                            lean_dec_ref_known(v___x_2626_, 1);
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
                    lean_dec_ref(v___y_2618_);
                    lean_dec_ref(v___y_2615_);
                    return v___y_2619_;
                }
            }
            14 => {
                if lean_obj_tag(v___y_2634_) == 0 {
                    lean_dec_ref_known(v___y_2634_, 1);
                    v___x_2635_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__141_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2636_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__142_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2637_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__144_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2638_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__145_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2633_);
                    v___x_2639_ = l_Lean_Parser_registerAlias(
                        v___x_2635_,
                        v___x_2636_,
                        v___x_2637_,
                        v___x_2638_,
                        v___y_2633_,
                    );
                    if lean_obj_tag(v___x_2639_) == 0 {
                        lean_dec_ref_known(v___x_2639_, 1);
                        v___x_2640_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__147_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2641_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2635_, v___x_2640_);
                        if lean_obj_tag(v___x_2641_) == 0 {
                            lean_dec_ref_known(v___x_2641_, 1);
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
                    lean_dec_ref(v___y_2633_);
                    lean_dec_ref(v___y_2630_);
                    return v___y_2634_;
                }
            }
            15 => {
                if lean_obj_tag(v___y_2647_) == 0 {
                    lean_dec_ref_known(v___y_2647_, 1);
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
                    if lean_obj_tag(v___x_2654_) == 0 {
                        lean_dec_ref_known(v___x_2654_, 1);
                        v___x_2655_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__158_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2656_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2648_, v___x_2655_);
                        if lean_obj_tag(v___x_2656_) == 0 {
                            lean_dec_ref_known(v___x_2656_, 1);
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
                    lean_dec_ref(v___y_2646_);
                    return v___y_2647_;
                }
            }
            16 => {
                if lean_obj_tag(v___y_2663_) == 0 {
                    lean_dec_ref_known(v___y_2663_, 1);
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
                    if lean_obj_tag(v___x_2668_) == 0 {
                        lean_dec_ref_known(v___x_2668_, 1);
                        v___x_2669_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__168_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2670_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2664_, v___x_2669_);
                        if lean_obj_tag(v___x_2670_) == 0 {
                            lean_dec_ref_known(v___x_2670_, 1);
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
                    lean_dec_ref(v___y_2661_);
                    return v___y_2663_;
                }
            }
            17 => {
                if lean_obj_tag(v___y_2676_) == 0 {
                    lean_dec_ref_known(v___y_2676_, 1);
                    v___x_2677_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__172_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2678_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__174_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2679_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__176_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2680_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__177_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2681_ = l_Lean_Parser_registerAlias(
                        v___x_2677_,
                        v___x_2678_,
                        v___x_2679_,
                        v___x_2680_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2681_) == 0 {
                        lean_dec_ref_known(v___x_2681_, 1);
                        v___x_2682_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__178_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2683_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2677_, v___x_2682_);
                        if lean_obj_tag(v___x_2683_) == 0 {
                            lean_dec_ref_known(v___x_2683_, 1);
                            v___x_2684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__179_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                    lean_dec_ref(v___y_2675_);
                    return v___y_2676_;
                }
            }
            18 => {
                if lean_obj_tag(v___y_2689_) == 0 {
                    lean_dec_ref_known(v___y_2689_, 1);
                    v___x_2690_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__181_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2691_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__183_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2692_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__185_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2693_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__186_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2694_ = l_Lean_Parser_registerAlias(
                        v___x_2690_,
                        v___x_2691_,
                        v___x_2692_,
                        v___x_2693_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2694_) == 0 {
                        lean_dec_ref_known(v___x_2694_, 1);
                        v___x_2695_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__187_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2696_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2690_, v___x_2695_);
                        if lean_obj_tag(v___x_2696_) == 0 {
                            lean_dec_ref_known(v___x_2696_, 1);
                            v___x_2697_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__188_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                    lean_dec_ref(v___y_2687_);
                    return v___y_2689_;
                }
            }
            19 => {
                if lean_obj_tag(v___y_2702_) == 0 {
                    lean_dec_ref_known(v___y_2702_, 1);
                    v___x_2703_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__190_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2704_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__192_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2705_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__194_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2706_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__195_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2707_ = l_Lean_Parser_registerAlias(
                        v___x_2703_,
                        v___x_2704_,
                        v___x_2705_,
                        v___x_2706_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2707_) == 0 {
                        lean_dec_ref_known(v___x_2707_, 1);
                        v___x_2708_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__196_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2709_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2703_, v___x_2708_);
                        if lean_obj_tag(v___x_2709_) == 0 {
                            lean_dec_ref_known(v___x_2709_, 1);
                            v___x_2710_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__197_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                    lean_dec_ref(v___y_2701_);
                    return v___y_2702_;
                }
            }
            20 => {
                if lean_obj_tag(v___y_2715_) == 0 {
                    lean_dec_ref_known(v___y_2715_, 1);
                    v___x_2716_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__199_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2717_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__201_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2718_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__203_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2719_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__204_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2720_ = l_Lean_Parser_registerAlias(
                        v___x_2716_,
                        v___x_2717_,
                        v___x_2718_,
                        v___x_2719_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2720_) == 0 {
                        lean_dec_ref_known(v___x_2720_, 1);
                        v___x_2721_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__205_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2722_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2716_, v___x_2721_);
                        if lean_obj_tag(v___x_2722_) == 0 {
                            lean_dec_ref_known(v___x_2722_, 1);
                            v___x_2723_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__206_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                    lean_dec_ref(v___y_2713_);
                    return v___y_2715_;
                }
            }
            21 => {
                if lean_obj_tag(v___y_2728_) == 0 {
                    lean_dec_ref_known(v___y_2728_, 1);
                    v___x_2729_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__208_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2730_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__209_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2731_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__210_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2732_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__211_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2727_);
                    v___x_2733_ = l_Lean_Parser_registerAlias(
                        v___x_2729_,
                        v___x_2730_,
                        v___x_2731_,
                        v___x_2732_,
                        v___y_2727_,
                    );
                    if lean_obj_tag(v___x_2733_) == 0 {
                        lean_dec_ref_known(v___x_2733_, 1);
                        v___x_2734_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__213_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2735_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2729_, v___x_2734_);
                        if lean_obj_tag(v___x_2735_) == 0 {
                            lean_dec_ref_known(v___x_2735_, 1);
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
                    lean_dec_ref(v___y_2727_);
                    return v___y_2728_;
                }
            }
            22 => {
                if lean_obj_tag(v___y_2742_) == 0 {
                    lean_dec_ref_known(v___y_2742_, 1);
                    v___x_2743_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__217_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2744_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__218_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2745_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__219_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    lean_inc_ref(v___y_2741_);
                    v___x_2746_ = l_Lean_Parser_registerAlias(
                        v___x_2743_,
                        v___x_2744_,
                        v___x_2745_,
                        v___y_2739_,
                        v___y_2741_,
                    );
                    if lean_obj_tag(v___x_2746_) == 0 {
                        lean_dec_ref_known(v___x_2746_, 1);
                        v___x_2747_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__221_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2748_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2743_, v___x_2747_);
                        if lean_obj_tag(v___x_2748_) == 0 {
                            lean_dec_ref_known(v___x_2748_, 1);
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
                    lean_dec_ref(v___y_2741_);
                    lean_dec(v___y_2739_);
                    return v___y_2742_;
                }
            }
            23 => {
                if lean_obj_tag(v___y_2754_) == 0 {
                    lean_dec_ref_known(v___y_2754_, 1);
                    v___x_2755_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__225_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2756_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__226_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2757_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__227_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2758_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__228_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2752_);
                    v___x_2759_ = l_Lean_Parser_registerAlias(
                        v___x_2755_,
                        v___x_2756_,
                        v___x_2757_,
                        v___x_2758_,
                        v___y_2752_,
                    );
                    if lean_obj_tag(v___x_2759_) == 0 {
                        lean_dec_ref_known(v___x_2759_, 1);
                        v___x_2760_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__230_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2761_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2755_, v___x_2760_);
                        if lean_obj_tag(v___x_2761_) == 0 {
                            lean_dec_ref_known(v___x_2761_, 1);
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
                    lean_dec_ref(v___y_2752_);
                    return v___y_2754_;
                }
            }
            24 => {
                if lean_obj_tag(v___y_2767_) == 0 {
                    lean_dec_ref_known(v___y_2767_, 1);
                    v___x_2768_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__234_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2769_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__236_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2770_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__237_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2771_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__238_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2766_);
                    v___x_2772_ = l_Lean_Parser_registerAlias(
                        v___x_2768_,
                        v___x_2769_,
                        v___x_2770_,
                        v___x_2771_,
                        v___y_2766_,
                    );
                    if lean_obj_tag(v___x_2772_) == 0 {
                        lean_dec_ref_known(v___x_2772_, 1);
                        v___x_2773_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__240_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2774_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2768_, v___x_2773_);
                        if lean_obj_tag(v___x_2774_) == 0 {
                            lean_dec_ref_known(v___x_2774_, 1);
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
                    lean_dec_ref(v___y_2766_);
                    return v___y_2767_;
                }
            }
            25 => {
                if lean_obj_tag(v___y_2780_) == 0 {
                    lean_dec_ref_known(v___y_2780_, 1);
                    v___x_2781_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__244_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2782_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__246_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2783_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__247_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2784_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__248_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2779_);
                    v___x_2785_ = l_Lean_Parser_registerAlias(
                        v___x_2781_,
                        v___x_2782_,
                        v___x_2783_,
                        v___x_2784_,
                        v___y_2779_,
                    );
                    if lean_obj_tag(v___x_2785_) == 0 {
                        lean_dec_ref_known(v___x_2785_, 1);
                        v___x_2786_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__250_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2787_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2781_, v___x_2786_);
                        if lean_obj_tag(v___x_2787_) == 0 {
                            lean_dec_ref_known(v___x_2787_, 1);
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
                    lean_dec_ref(v___y_2779_);
                    return v___y_2780_;
                }
            }
            26 => {
                if lean_obj_tag(v___y_2793_) == 0 {
                    lean_dec_ref_known(v___y_2793_, 1);
                    v___x_2794_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__254_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2795_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__256_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2796_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__257_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2797_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__258_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2792_);
                    v___x_2798_ = l_Lean_Parser_registerAlias(
                        v___x_2794_,
                        v___x_2795_,
                        v___x_2796_,
                        v___x_2797_,
                        v___y_2792_,
                    );
                    if lean_obj_tag(v___x_2798_) == 0 {
                        lean_dec_ref_known(v___x_2798_, 1);
                        v___x_2799_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__260_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2800_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2794_, v___x_2799_);
                        if lean_obj_tag(v___x_2800_) == 0 {
                            lean_dec_ref_known(v___x_2800_, 1);
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
                    lean_dec_ref(v___y_2792_);
                    return v___y_2793_;
                }
            }
            27 => {
                if lean_obj_tag(v___y_2806_) == 0 {
                    lean_dec_ref_known(v___y_2806_, 1);
                    v___x_2807_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__264_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2808_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__266_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2809_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__267_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2810_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__268_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    lean_inc_ref(v___y_2805_);
                    v___x_2811_ = l_Lean_Parser_registerAlias(
                        v___x_2807_,
                        v___x_2808_,
                        v___x_2809_,
                        v___x_2810_,
                        v___y_2805_,
                    );
                    if lean_obj_tag(v___x_2811_) == 0 {
                        lean_dec_ref_known(v___x_2811_, 1);
                        v___x_2812_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__270_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2813_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2807_, v___x_2812_);
                        if lean_obj_tag(v___x_2813_) == 0 {
                            lean_dec_ref_known(v___x_2813_, 1);
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
                    lean_dec_ref(v___y_2805_);
                    return v___y_2806_;
                }
            }
            28 => {
                if lean_obj_tag(v___y_2817_) == 0 {
                    lean_dec_ref_known(v___y_2817_, 1);
                    v___x_2818_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__274_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2819_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__276_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2820_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__277_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                    if lean_obj_tag(v___x_2824_) == 0 {
                        lean_dec_ref_known(v___x_2824_, 1);
                        v___x_2825_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__282_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2826_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2818_, v___x_2825_);
                        if lean_obj_tag(v___x_2826_) == 0 {
                            lean_dec_ref_known(v___x_2826_, 1);
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
                if lean_obj_tag(v___y_2830_) == 0 {
                    lean_dec_ref_known(v___y_2830_, 1);
                    v___x_2831_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__286_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2832_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__288_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2833_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__291_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2834_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__292_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2835_ = l_Lean_Parser_registerAlias(
                        v___x_2831_,
                        v___x_2832_,
                        v___x_2833_,
                        v___x_2834_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2835_) == 0 {
                        lean_dec_ref_known(v___x_2835_, 1);
                        v___x_2836_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__293_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                        v___x_2837_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2831_, v___x_2836_);
                        if lean_obj_tag(v___x_2837_) == 0 {
                            lean_dec_ref_known(v___x_2837_, 1);
                            v___x_2838_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__294_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
                if lean_obj_tag(v___y_2841_) == 0 {
                    lean_dec_ref_known(v___y_2841_, 1);
                    v___x_2842_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__296_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2843_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__298_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2844_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__301_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
                    v___x_2845_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__302_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                    v___x_2846_ = l_Lean_Parser_registerAlias(
                        v___x_2842_,
                        v___x_2843_,
                        v___x_2844_,
                        v___x_2845_,
                        v___x_2659_,
                    );
                    if lean_obj_tag(v___x_2846_) == 0 {
                        lean_dec_ref_known(v___x_2846_, 1);
                        v___x_2847_ = l___private_Lean_Parser_0__Lean_Parser_initFn___closed__303_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_;
                        v___x_2848_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_2842_, v___x_2847_);
                        if lean_obj_tag(v___x_2848_) == 0 {
                            lean_dec_ref_known(v___x_2848_, 1);
                            v___x_2849_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_0__Lean_Parser_initFn___closed__304_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_);
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
    mut v_a_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2857_: *mut LeanObject = core::ptr::null_mut();
    v_res_2857_ = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
    return v_res_2857_;
}
pub unsafe fn lean_mk_antiquot_parenthesizer(
    mut v_name_2858_: *mut LeanObject,
    mut v_kind_2859_: *mut LeanObject,
    mut v_anonymous_2860_: u8,
    mut v_isPseudoKind_2861_: u8,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2865_);
    lean_dec_ref(v_a_2864_);
    lean_dec(v_a_2863_);
    lean_dec_ref(v_a_2862_);
    return v___x_2867_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer___boxed(
    mut v_name_2868_: *mut LeanObject,
    mut v_kind_2869_: *mut LeanObject,
    mut v_anonymous_2870_: *mut LeanObject,
    mut v_isPseudoKind_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
    mut v_a_2876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_2877_: u8 = 0;
    let mut v_isPseudoKind_boxed_2878_: u8 = 0;
    let mut v_res_2879_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_2877_ = (lean_unbox(v_anonymous_2870_) as u8);
    v_isPseudoKind_boxed_2878_ = (lean_unbox(v_isPseudoKind_2871_) as u8);
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
    mut v_a_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    v___x_2885_ =
        l_Lean_Parser_Term_ident_parenthesizer(v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_);
    return v___x_2885_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___boxed(
    mut v_a_2886_: *mut LeanObject,
    mut v_a_2887_: *mut LeanObject,
    mut v_a_2888_: *mut LeanObject,
    mut v_a_2889_: *mut LeanObject,
    mut v_a_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer(
        v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_,
    );
    lean_dec(v_a_2889_);
    lean_dec_ref(v_a_2888_);
    lean_dec(v_a_2887_);
    lean_dec_ref(v_a_2886_);
    return v_res_2891_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1()
-> *mut LeanObject {
    let mut v___f_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2909_: *mut LeanObject = core::ptr::null_mut();
    v_res_2909_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
    return v_res_2909_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(
    mut v_a_2910_: *mut LeanObject,
    mut v_a_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_a_2913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Parser_Term_num_parenthesizer(v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
    return v___x_2915_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___boxed(
    mut v_a_2916_: *mut LeanObject,
    mut v_a_2917_: *mut LeanObject,
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer(
        v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_,
    );
    lean_dec(v_a_2919_);
    lean_dec_ref(v_a_2918_);
    lean_dec(v_a_2917_);
    lean_dec_ref(v_a_2916_);
    return v_res_2921_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1()
-> *mut LeanObject {
    let mut v___f_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2936_: *mut LeanObject = core::ptr::null_mut();
    v_res_2936_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
    return v_res_2936_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    v___x_2942_ =
        l_Lean_Parser_Term_scientific_parenthesizer(v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
    return v___x_2942_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___boxed(
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2948_: *mut LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer(
        v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_,
    );
    lean_dec(v_a_2946_);
    lean_dec_ref(v_a_2945_);
    lean_dec(v_a_2944_);
    lean_dec_ref(v_a_2943_);
    return v_res_2948_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1()
-> *mut LeanObject {
    let mut v___f_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2963_: *mut LeanObject = core::ptr::null_mut();
    v_res_2963_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
    return v_res_2963_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Lean_Parser_Term_char_parenthesizer(v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_);
    return v___x_2969_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___boxed(
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2975_: *mut LeanObject = core::ptr::null_mut();
    v_res_2975_ = l_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer(
        v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
    );
    lean_dec(v_a_2973_);
    lean_dec_ref(v_a_2972_);
    lean_dec(v_a_2971_);
    lean_dec_ref(v_a_2970_);
    return v_res_2975_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1()
-> *mut LeanObject {
    let mut v___f_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2990_: *mut LeanObject = core::ptr::null_mut();
    v_res_2990_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
    return v_res_2990_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    v___x_2996_ = l_Lean_Parser_Term_str_parenthesizer(v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
    return v___x_2996_;
}
pub unsafe fn l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___boxed(
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3002_: *mut LeanObject = core::ptr::null_mut();
    v_res_3002_ = l_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer(
        v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
    );
    lean_dec(v_a_3000_);
    lean_dec_ref(v_a_2999_);
    lean_dec(v_a_2998_);
    lean_dec_ref(v_a_2997_);
    return v_res_3002_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1()
-> *mut LeanObject {
    let mut v___f_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3017_: *mut LeanObject = core::ptr::null_mut();
    v_res_3017_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
    return v_res_3017_;
}
pub unsafe fn lean_pretty_printer_parenthesizer_interpret_parser_descr(
    mut v_x_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
    mut v_a_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3025_: u8 = 0;
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_a_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v_ref_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_name_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3064_: u8 = 0;
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3069_: u8 = 0;
    let mut v_a_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v_ref_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3084_: u8 = 0;
    let mut v_isSharedCheck_3085_: u8 = 0;
    let mut v_name_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_a_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v_ref_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_kind_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prec_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_kind_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prec_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v_val_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_val_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_includeIdent_3154_: u8 = 0;
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_catName_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rbp_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_p_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sep_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_psep_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3187_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_p_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sep_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_psep_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3204_: u8 = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_val_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asciiVal_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preserveForPP_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3018_) {
                0 => {
                    lean_dec(v_a_3020_);
                    v_name_3022_ = lean_ctor_get(v_x_3018_, 0);
                    v_isSharedCheck_3051_ = (!lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3051_ == 0 {
                        v___x_3024_ = v_x_3018_;
                        v_isShared_3025_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_name_3022_);
                        lean_dec(v_x_3018_);
                        v___x_3024_ = lean_box(0);
                        v_isShared_3025_ = v_isSharedCheck_3051_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_name_3052_ = lean_ctor_get(v_x_3018_, 0);
                    v_p_3053_ = lean_ctor_get(v_x_3018_, 1);
                    v_isSharedCheck_3085_ = (!lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3085_ == 0 {
                        v___x_3055_ = v_x_3018_;
                        v_isShared_3056_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_p_3053_);
                        lean_inc(v_name_3052_);
                        lean_dec(v_x_3018_);
                        v___x_3055_ = lean_box(0);
                        v_isShared_3056_ = v_isSharedCheck_3085_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_name_3086_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc(v_name_3086_);
                    v_p_u2081_3087_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc_ref(v_p_u2081_3087_);
                    v_p_u2082_3088_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc_ref(v_p_u2082_3088_);
                    lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3089_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
                    v___x_3090_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_3089_, v_name_3086_);
                    if lean_obj_tag(v___x_3090_) == 0 {
                        v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
                        lean_inc(v_a_3091_);
                        lean_dec_ref_known(v___x_3090_, 1);
                        lean_inc(v_a_3020_);
                        lean_inc_ref(v_a_3019_);
                        v___x_3092_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_p_u2081_3087_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if lean_obj_tag(v___x_3092_) == 0 {
                            v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
                            lean_inc(v_a_3093_);
                            lean_dec_ref_known(v___x_3092_, 1);
                            v___x_3094_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                                v_p_u2082_3088_,
                                v_a_3019_,
                                v_a_3020_,
                            );
                            if lean_obj_tag(v___x_3094_) == 0 {
                                v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
                                v_isSharedCheck_3103_ = (!lean_is_exclusive(v___x_3094_)) as u8;
                                if v_isSharedCheck_3103_ == 0 {
                                    v___x_3097_ = v___x_3094_;
                                    v_isShared_3098_ = v_isSharedCheck_3103_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_3095_);
                                    lean_dec(v___x_3094_);
                                    v___x_3097_ = lean_box(0);
                                    v_isShared_3098_ = v_isSharedCheck_3103_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3093_);
                                lean_dec(v_a_3091_);
                                return v___x_3094_;
                            }
                        } else {
                            lean_dec(v_a_3091_);
                            lean_dec_ref(v_p_u2082_3088_);
                            lean_dec(v_a_3020_);
                            lean_dec_ref(v_a_3019_);
                            return v___x_3092_;
                        }
                    } else {
                        lean_dec_ref(v_p_u2082_3088_);
                        lean_dec_ref(v_p_u2081_3087_);
                        lean_dec(v_a_3020_);
                        v_a_3104_ = lean_ctor_get(v___x_3090_, 0);
                        v_isSharedCheck_3116_ = (!lean_is_exclusive(v___x_3090_)) as u8;
                        if v_isSharedCheck_3116_ == 0 {
                            v___x_3106_ = v___x_3090_;
                            v_isShared_3107_ = v_isSharedCheck_3116_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3104_);
                            lean_dec(v___x_3090_);
                            v___x_3106_ = lean_box(0);
                            v_isShared_3107_ = v_isSharedCheck_3116_;
                            state = 15;
                            continue;
                        }
                    }
                }
                3 => {
                    v_kind_3117_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc(v_kind_3117_);
                    v_prec_3118_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc(v_prec_3118_);
                    v_p_3119_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc_ref(v_p_3119_);
                    lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3120_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3119_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3120_) == 0 {
                        v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
                        v_isSharedCheck_3129_ = (!lean_is_exclusive(v___x_3120_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v___x_3123_ = v___x_3120_;
                            v_isShared_3124_ = v_isSharedCheck_3129_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3121_);
                            lean_dec(v___x_3120_);
                            v___x_3123_ = lean_box(0);
                            v_isShared_3124_ = v_isSharedCheck_3129_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v_prec_3118_);
                        lean_dec(v_kind_3117_);
                        return v___x_3120_;
                    }
                }
                4 => {
                    v_kind_3130_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc(v_kind_3130_);
                    v_prec_3131_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc(v_prec_3131_);
                    v_lhsPrec_3132_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc(v_lhsPrec_3132_);
                    v_p_3133_ = lean_ctor_get(v_x_3018_, 3);
                    lean_inc_ref(v_p_3133_);
                    lean_dec_ref_known(v_x_3018_, 4);
                    v___x_3134_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3133_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3134_) == 0 {
                        v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
                        v_isSharedCheck_3143_ = (!lean_is_exclusive(v___x_3134_)) as u8;
                        if v_isSharedCheck_3143_ == 0 {
                            v___x_3137_ = v___x_3134_;
                            v_isShared_3138_ = v_isSharedCheck_3143_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_3135_);
                            lean_dec(v___x_3134_);
                            v___x_3137_ = lean_box(0);
                            v_isShared_3138_ = v_isSharedCheck_3143_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_dec(v_lhsPrec_3132_);
                        lean_dec(v_prec_3131_);
                        lean_dec(v_kind_3130_);
                        return v___x_3134_;
                    }
                }
                5 => {
                    lean_dec(v_a_3020_);
                    lean_dec_ref(v_a_3019_);
                    v_val_3144_ = lean_ctor_get(v_x_3018_, 0);
                    v_isSharedCheck_3152_ = (!lean_is_exclusive(v_x_3018_)) as u8;
                    if v_isSharedCheck_3152_ == 0 {
                        v___x_3146_ = v_x_3018_;
                        v_isShared_3147_ = v_isSharedCheck_3152_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_val_3144_);
                        lean_dec(v_x_3018_);
                        v___x_3146_ = lean_box(0);
                        v_isShared_3147_ = v_isSharedCheck_3152_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    lean_dec(v_a_3020_);
                    lean_dec_ref(v_a_3019_);
                    v_val_3153_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc_ref(v_val_3153_);
                    v_includeIdent_3154_ = lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_x_3018_, 1);
                    v___x_3155_ = lean_box((v_includeIdent_3154_) as usize);
                    v___x_3156_ = lean_alloc_closure(
                        l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    lean_closure_set(v___x_3156_, 0, v_val_3153_);
                    lean_closure_set(v___x_3156_, 1, v___x_3155_);
                    v___x_3157_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3157_, 0, v___x_3156_);
                    return v___x_3157_;
                }
                7 => {
                    lean_dec(v_a_3020_);
                    lean_dec_ref(v_a_3019_);
                    v_catName_3158_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc(v_catName_3158_);
                    v_rbp_3159_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc(v_rbp_3159_);
                    lean_dec_ref_known(v_x_3018_, 2);
                    v___x_3160_ = lean_alloc_closure(
                        l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer___boxed
                            as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    lean_closure_set(v___x_3160_, 0, v_catName_3158_);
                    lean_closure_set(v___x_3160_, 1, v_rbp_3159_);
                    v___x_3161_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3161_, 0, v___x_3160_);
                    return v___x_3161_;
                }
                8 => {
                    v_declName_3162_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc(v_declName_3162_);
                    lean_dec_ref_known(v_x_3018_, 1);
                    v___x_3163_ = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
                    v___x_3164_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
                        v___x_3163_,
                        v_declName_3162_,
                        v_a_3019_,
                        v_a_3020_,
                    );
                    lean_dec(v_a_3020_);
                    lean_dec_ref(v_a_3019_);
                    return v___x_3164_;
                }
                9 => {
                    v_name_3165_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc_ref(v_name_3165_);
                    v_kind_3166_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc(v_kind_3166_);
                    v_p_3167_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc_ref(v_p_3167_);
                    lean_dec_ref_known(v_x_3018_, 3);
                    v___x_3168_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3167_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3168_) == 0 {
                        v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
                        v_isSharedCheck_3183_ = (!lean_is_exclusive(v___x_3168_)) as u8;
                        if v_isSharedCheck_3183_ == 0 {
                            v___x_3171_ = v___x_3168_;
                            v_isShared_3172_ = v_isSharedCheck_3183_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3169_);
                            lean_dec(v___x_3168_);
                            v___x_3171_ = lean_box(0);
                            v_isShared_3172_ = v_isSharedCheck_3183_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec(v_kind_3166_);
                        lean_dec_ref(v_name_3165_);
                        return v___x_3168_;
                    }
                }
                10 => {
                    v_p_3184_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc_ref(v_p_3184_);
                    v_sep_3185_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc_ref(v_sep_3185_);
                    v_psep_3186_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc_ref(v_psep_3186_);
                    v_allowTrailingSep_3187_ = lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref_known(v_x_3018_, 3);
                    lean_inc(v_a_3020_);
                    lean_inc_ref(v_a_3019_);
                    v___x_3188_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3184_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3188_) == 0 {
                        v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
                        lean_inc(v_a_3189_);
                        lean_dec_ref_known(v___x_3188_, 1);
                        v___x_3190_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_psep_3186_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if lean_obj_tag(v___x_3190_) == 0 {
                            v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
                            v_isSharedCheck_3200_ = (!lean_is_exclusive(v___x_3190_)) as u8;
                            if v_isSharedCheck_3200_ == 0 {
                                v___x_3193_ = v___x_3190_;
                                v_isShared_3194_ = v_isSharedCheck_3200_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3191_);
                                lean_dec(v___x_3190_);
                                v___x_3193_ = lean_box(0);
                                v_isShared_3194_ = v_isSharedCheck_3200_;
                                state = 25;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3189_);
                            lean_dec_ref(v_sep_3185_);
                            return v___x_3190_;
                        }
                    } else {
                        lean_dec_ref(v_psep_3186_);
                        lean_dec_ref(v_sep_3185_);
                        lean_dec(v_a_3020_);
                        lean_dec_ref(v_a_3019_);
                        return v___x_3188_;
                    }
                }
                11 => {
                    v_p_3201_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc_ref(v_p_3201_);
                    v_sep_3202_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc_ref(v_sep_3202_);
                    v_psep_3203_ = lean_ctor_get(v_x_3018_, 2);
                    lean_inc_ref(v_psep_3203_);
                    v_allowTrailingSep_3204_ = lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref_known(v_x_3018_, 3);
                    lean_inc(v_a_3020_);
                    lean_inc_ref(v_a_3019_);
                    v___x_3205_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3201_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3205_) == 0 {
                        v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
                        lean_inc(v_a_3206_);
                        lean_dec_ref_known(v___x_3205_, 1);
                        v___x_3207_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                            v_psep_3203_,
                            v_a_3019_,
                            v_a_3020_,
                        );
                        if lean_obj_tag(v___x_3207_) == 0 {
                            v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
                            v_isSharedCheck_3217_ = (!lean_is_exclusive(v___x_3207_)) as u8;
                            if v_isSharedCheck_3217_ == 0 {
                                v___x_3210_ = v___x_3207_;
                                v_isShared_3211_ = v_isSharedCheck_3217_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_3208_);
                                lean_dec(v___x_3207_);
                                v___x_3210_ = lean_box(0);
                                v_isShared_3211_ = v_isSharedCheck_3217_;
                                state = 27;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3206_);
                            lean_dec_ref(v_sep_3202_);
                            return v___x_3207_;
                        }
                    } else {
                        lean_dec_ref(v_psep_3203_);
                        lean_dec_ref(v_sep_3202_);
                        lean_dec(v_a_3020_);
                        lean_dec_ref(v_a_3019_);
                        return v___x_3205_;
                    }
                }
                _ => {
                    lean_dec(v_a_3020_);
                    lean_dec_ref(v_a_3019_);
                    v_val_3218_ = lean_ctor_get(v_x_3018_, 0);
                    lean_inc_ref(v_val_3218_);
                    v_asciiVal_3219_ = lean_ctor_get(v_x_3018_, 1);
                    lean_inc_ref(v_asciiVal_3219_);
                    v_preserveForPP_3220_ = lean_ctor_get_uint8(
                        v_x_3018_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec_ref_known(v_x_3018_, 2);
                    v___x_3221_ = lean_box((v_preserveForPP_3220_) as usize);
                    v___x_3222_ = lean_alloc_closure(
                        l_Lean_Parser_unicodeSymbol_parenthesizer___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    lean_closure_set(v___x_3222_, 0, v_val_3218_);
                    lean_closure_set(v___x_3222_, 1, v_asciiVal_3219_);
                    lean_closure_set(v___x_3222_, 2, v___x_3221_);
                    v___x_3223_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3223_, 0, v___x_3222_);
                    return v___x_3223_;
                }
            },
            1 => {
                v___x_3026_ = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerAliasesRef;
                v___x_3027_ = l_Lean_Parser_getConstAlias___redArg(v___x_3026_, v_name_3022_);
                if lean_obj_tag(v___x_3027_) == 0 {
                    lean_del_object(v___x_3024_);
                    lean_dec_ref(v_a_3019_);
                    v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3035_ = (!lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v___x_3030_ = v___x_3027_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3028_);
                        lean_dec(v___x_3027_);
                        v___x_3030_ = lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3036_ = lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3050_ = (!lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3038_ = v___x_3027_;
                        v_isShared_3039_ = v_isSharedCheck_3050_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3036_);
                        lean_dec(v___x_3027_);
                        v___x_3038_ = lean_box(0);
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
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3033_;
            }
            4 => {
                v_ref_3040_ = lean_ctor_get(v_a_3019_, 5);
                lean_inc(v_ref_3040_);
                lean_dec_ref(v_a_3019_);
                v___x_3041_ = lean_io_error_to_string(v_a_3036_);
                if v_isShared_3025_ == 0 {
                    lean_ctor_set_tag(v___x_3024_, 3);
                    lean_ctor_set(v___x_3024_, 0, v___x_3041_);
                    v___x_3043_ = v___x_3024_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3041_);
                    v___x_3043_ = v_reuseFailAlloc_3049_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3044_ = l_Lean_MessageData_ofFormat(v___x_3043_);
                v___x_3045_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3045_, 0, v_ref_3040_);
                lean_ctor_set(v___x_3045_, 1, v___x_3044_);
                if v_isShared_3039_ == 0 {
                    lean_ctor_set(v___x_3038_, 0, v___x_3045_);
                    v___x_3047_ = v___x_3038_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
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
                if lean_obj_tag(v___x_3058_) == 0 {
                    lean_del_object(v___x_3055_);
                    v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
                    lean_inc(v_a_3059_);
                    lean_dec_ref_known(v___x_3058_, 1);
                    v___x_3060_ = lean_pretty_printer_parenthesizer_interpret_parser_descr(
                        v_p_3053_, v_a_3019_, v_a_3020_,
                    );
                    if lean_obj_tag(v___x_3060_) == 0 {
                        v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
                        v_isSharedCheck_3069_ = (!lean_is_exclusive(v___x_3060_)) as u8;
                        if v_isSharedCheck_3069_ == 0 {
                            v___x_3063_ = v___x_3060_;
                            v_isShared_3064_ = v_isSharedCheck_3069_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3061_);
                            lean_dec(v___x_3060_);
                            v___x_3063_ = lean_box(0);
                            v_isShared_3064_ = v_isSharedCheck_3069_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3059_);
                        return v___x_3060_;
                    }
                } else {
                    lean_dec_ref(v_p_3053_);
                    lean_dec(v_a_3020_);
                    v_a_3070_ = lean_ctor_get(v___x_3058_, 0);
                    v_isSharedCheck_3084_ = (!lean_is_exclusive(v___x_3058_)) as u8;
                    if v_isSharedCheck_3084_ == 0 {
                        v___x_3072_ = v___x_3058_;
                        v_isShared_3073_ = v_isSharedCheck_3084_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3070_);
                        lean_dec(v___x_3058_);
                        v___x_3072_ = lean_box(0);
                        v_isShared_3073_ = v_isSharedCheck_3084_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3065_ = lean_apply_1(v_a_3059_, v_a_3061_);
                if v_isShared_3064_ == 0 {
                    lean_ctor_set(v___x_3063_, 0, v___x_3065_);
                    v___x_3067_ = v___x_3063_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
                    v___x_3067_ = v_reuseFailAlloc_3068_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3067_;
            }
            10 => {
                v_ref_3074_ = lean_ctor_get(v_a_3019_, 5);
                lean_inc(v_ref_3074_);
                lean_dec_ref(v_a_3019_);
                v___x_3075_ = lean_io_error_to_string(v_a_3070_);
                v___x_3076_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3076_, 0, v___x_3075_);
                v___x_3077_ = l_Lean_MessageData_ofFormat(v___x_3076_);
                if v_isShared_3056_ == 0 {
                    lean_ctor_set_tag(v___x_3055_, 0);
                    lean_ctor_set(v___x_3055_, 1, v___x_3077_);
                    lean_ctor_set(v___x_3055_, 0, v_ref_3074_);
                    v___x_3079_ = v___x_3055_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_ref_3074_);
                    lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3077_);
                    v___x_3079_ = v_reuseFailAlloc_3083_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3073_ == 0 {
                    lean_ctor_set(v___x_3072_, 0, v___x_3079_);
                    v___x_3081_ = v___x_3072_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3079_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3081_;
            }
            13 => {
                v___x_3099_ = lean_apply_2(v_a_3091_, v_a_3093_, v_a_3095_);
                if v_isShared_3098_ == 0 {
                    lean_ctor_set(v___x_3097_, 0, v___x_3099_);
                    v___x_3101_ = v___x_3097_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
                    v___x_3101_ = v_reuseFailAlloc_3102_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3101_;
            }
            15 => {
                v_ref_3108_ = lean_ctor_get(v_a_3019_, 5);
                lean_inc(v_ref_3108_);
                lean_dec_ref(v_a_3019_);
                v___x_3109_ = lean_io_error_to_string(v_a_3104_);
                v___x_3110_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3110_, 0, v___x_3109_);
                v___x_3111_ = l_Lean_MessageData_ofFormat(v___x_3110_);
                v___x_3112_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3112_, 0, v_ref_3108_);
                lean_ctor_set(v___x_3112_, 1, v___x_3111_);
                if v_isShared_3107_ == 0 {
                    lean_ctor_set(v___x_3106_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3106_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3114_;
            }
            17 => {
                v___x_3125_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___x_3125_, 0, v_kind_3117_);
                lean_closure_set(v___x_3125_, 1, v_prec_3118_);
                lean_closure_set(v___x_3125_, 2, v_a_3121_);
                if v_isShared_3124_ == 0 {
                    lean_ctor_set(v___x_3123_, 0, v___x_3125_);
                    v___x_3127_ = v___x_3123_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3127_;
            }
            19 => {
                v___x_3139_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3139_, 0, v_kind_3130_);
                lean_closure_set(v___x_3139_, 1, v_prec_3131_);
                lean_closure_set(v___x_3139_, 2, v_lhsPrec_3132_);
                lean_closure_set(v___x_3139_, 3, v_a_3135_);
                if v_isShared_3138_ == 0 {
                    lean_ctor_set(v___x_3137_, 0, v___x_3139_);
                    v___x_3141_ = v___x_3137_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3141_;
            }
            21 => {
                v___x_3148_ = lean_alloc_closure(
                    l_Lean_Parser_symbol_parenthesizer___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___x_3148_, 0, v_val_3144_);
                if v_isShared_3147_ == 0 {
                    lean_ctor_set_tag(v___x_3146_, 0);
                    lean_ctor_set(v___x_3146_, 0, v___x_3148_);
                    v___x_3150_ = v___x_3146_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
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
                v___x_3175_ = lean_box((v___x_3173_) as usize);
                v___x_3176_ = lean_box((v___x_3174_) as usize);
                lean_inc(v_kind_3166_);
                v___x_3177_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_mkAntiquot_parenthesizer_x27___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3177_, 0, v_name_3165_);
                lean_closure_set(v___x_3177_, 1, v_kind_3166_);
                lean_closure_set(v___x_3177_, 2, v___x_3175_);
                lean_closure_set(v___x_3177_, 3, v___x_3176_);
                v___x_3178_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_3178_, 0, v_kind_3166_);
                lean_closure_set(v___x_3178_, 1, v_a_3169_);
                v___x_3179_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_3179_, 0, v___x_3177_);
                lean_closure_set(v___x_3179_, 1, v___x_3178_);
                if v_isShared_3172_ == 0 {
                    lean_ctor_set(v___x_3171_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3171_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3181_;
            }
            25 => {
                v___x_3195_ = lean_box((v_allowTrailingSep_3187_) as usize);
                v___x_3196_ = lean_alloc_closure(
                    l_Lean_Parser_sepBy_parenthesizer___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3196_, 0, v_a_3189_);
                lean_closure_set(v___x_3196_, 1, v_sep_3185_);
                lean_closure_set(v___x_3196_, 2, v_a_3191_);
                lean_closure_set(v___x_3196_, 3, v___x_3195_);
                if v_isShared_3194_ == 0 {
                    lean_ctor_set(v___x_3193_, 0, v___x_3196_);
                    v___x_3198_ = v___x_3193_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3198_;
            }
            27 => {
                v___x_3212_ = lean_box((v_allowTrailingSep_3204_) as usize);
                v___x_3213_ = lean_alloc_closure(
                    l_Lean_Parser_sepBy1_parenthesizer___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3213_, 0, v_a_3206_);
                lean_closure_set(v___x_3213_, 1, v_sep_3202_);
                lean_closure_set(v___x_3213_, 2, v_a_3208_);
                lean_closure_set(v___x_3213_, 3, v___x_3212_);
                if v_isShared_3211_ == 0 {
                    lean_ctor_set(v___x_3210_, 0, v___x_3213_);
                    v___x_3215_ = v___x_3210_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
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
    mut v_x_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3228_: *mut LeanObject = core::ptr::null_mut();
    v_res_3228_ =
        lean_pretty_printer_parenthesizer_interpret_parser_descr(v_x_3224_, v_a_3225_, v_a_3226_);
    return v_res_3228_;
}
pub unsafe fn lean_mk_antiquot_formatter(
    mut v_name_3229_: *mut LeanObject,
    mut v_kind_3230_: *mut LeanObject,
    mut v_anonymous_3231_: u8,
    mut v_isPseudoKind_3232_: u8,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3236_);
    lean_dec_ref(v_a_3235_);
    lean_dec(v_a_3234_);
    lean_dec_ref(v_a_3233_);
    return v___x_3238_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter___boxed(
    mut v_name_3239_: *mut LeanObject,
    mut v_kind_3240_: *mut LeanObject,
    mut v_anonymous_3241_: *mut LeanObject,
    mut v_isPseudoKind_3242_: *mut LeanObject,
    mut v_a_3243_: *mut LeanObject,
    mut v_a_3244_: *mut LeanObject,
    mut v_a_3245_: *mut LeanObject,
    mut v_a_3246_: *mut LeanObject,
    mut v_a_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_anonymous_boxed_3248_: u8 = 0;
    let mut v_isPseudoKind_boxed_3249_: u8 = 0;
    let mut v_res_3250_: *mut LeanObject = core::ptr::null_mut();
    v_anonymous_boxed_3248_ = (lean_unbox(v_anonymous_3241_) as u8);
    v_isPseudoKind_boxed_3249_ = (lean_unbox(v_isPseudoKind_3242_) as u8);
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
    mut v_a_3251_: *mut LeanObject,
    mut v_a_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_Parser_Term_ident_formatter(v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_ident_formatter___boxed(
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3262_: *mut LeanObject = core::ptr::null_mut();
    v_res_3262_ =
        l_Lean_PrettyPrinter_Formatter_ident_formatter(v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
    lean_dec(v_a_3260_);
    lean_dec_ref(v_a_3259_);
    lean_dec(v_a_3258_);
    lean_dec_ref(v_a_3257_);
    return v_res_3262_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1()
-> *mut LeanObject {
    let mut v___f_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3279_: *mut LeanObject = core::ptr::null_mut();
    v_res_3279_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
    return v_res_3279_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_numLit_formatter(
    mut v_a_3280_: *mut LeanObject,
    mut v_a_3281_: *mut LeanObject,
    mut v_a_3282_: *mut LeanObject,
    mut v_a_3283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_Parser_Term_num_formatter(v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_);
    return v___x_3285_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_numLit_formatter___boxed(
    mut v_a_3286_: *mut LeanObject,
    mut v_a_3287_: *mut LeanObject,
    mut v_a_3288_: *mut LeanObject,
    mut v_a_3289_: *mut LeanObject,
    mut v_a_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3291_: *mut LeanObject = core::ptr::null_mut();
    v_res_3291_ =
        l_Lean_PrettyPrinter_Formatter_numLit_formatter(v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_);
    lean_dec(v_a_3289_);
    lean_dec_ref(v_a_3288_);
    lean_dec(v_a_3287_);
    lean_dec_ref(v_a_3286_);
    return v_res_3291_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1()
-> *mut LeanObject {
    let mut v___f_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3306_: *mut LeanObject = core::ptr::null_mut();
    v_res_3306_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
    return v_res_3306_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(
    mut v_a_3307_: *mut LeanObject,
    mut v_a_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    v___x_3312_ =
        l_Lean_Parser_Term_scientific_formatter(v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_);
    return v___x_3312_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_scientificLit_formatter___boxed(
    mut v_a_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3318_: *mut LeanObject = core::ptr::null_mut();
    v_res_3318_ = l_Lean_PrettyPrinter_Formatter_scientificLit_formatter(
        v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_,
    );
    lean_dec(v_a_3316_);
    lean_dec_ref(v_a_3315_);
    lean_dec(v_a_3314_);
    lean_dec_ref(v_a_3313_);
    return v_res_3318_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1()
-> *mut LeanObject {
    let mut v___f_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
    return v_res_3333_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_charLit_formatter(
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Lean_Parser_Term_char_formatter(v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_charLit_formatter___boxed(
    mut v_a_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3345_: *mut LeanObject = core::ptr::null_mut();
    v_res_3345_ = l_Lean_PrettyPrinter_Formatter_charLit_formatter(
        v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_,
    );
    lean_dec(v_a_3343_);
    lean_dec_ref(v_a_3342_);
    lean_dec(v_a_3341_);
    lean_dec_ref(v_a_3340_);
    return v_res_3345_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1()
-> *mut LeanObject {
    let mut v___f_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3360_: *mut LeanObject = core::ptr::null_mut();
    v_res_3360_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
    return v_res_3360_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_strLit_formatter(
    mut v_a_3361_: *mut LeanObject,
    mut v_a_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    v___x_3366_ = l_Lean_Parser_Term_str_formatter(v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
    return v___x_3366_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_strLit_formatter___boxed(
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
    mut v_a_3370_: *mut LeanObject,
    mut v_a_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3372_: *mut LeanObject = core::ptr::null_mut();
    v_res_3372_ =
        l_Lean_PrettyPrinter_Formatter_strLit_formatter(v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_);
    lean_dec(v_a_3370_);
    lean_dec_ref(v_a_3369_);
    lean_dec(v_a_3368_);
    lean_dec_ref(v_a_3367_);
    return v_res_3372_;
}
pub unsafe fn l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1()
-> *mut LeanObject {
    let mut v___f_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3387_: *mut LeanObject = core::ptr::null_mut();
    v_res_3387_ = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
    return v_res_3387_;
}
pub unsafe fn l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(
    mut v___x_3388_: *mut LeanObject,
    mut v___x_3389_: *mut LeanObject,
    mut v___y_3390_: *mut LeanObject,
    mut v___y_3391_: *mut LeanObject,
    mut v___y_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_3396_: *mut LeanObject,
    mut v___x_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3403_: *mut LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0(
        v___x_3396_,
        v___x_3397_,
        v___y_3398_,
        v___y_3399_,
        v___y_3400_,
        v___y_3401_,
    );
    lean_dec(v___y_3401_);
    lean_dec_ref(v___y_3400_);
    lean_dec(v___y_3399_);
    lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn lean_pretty_printer_formatter_interpret_parser_descr(
    mut v_x_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_a_3406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3421_: u8 = 0;
    let mut v_a_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v_ref_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut v_name_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_a_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3459_: u8 = 0;
    let mut v_ref_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3470_: u8 = 0;
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_name_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3484_: u8 = 0;
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut v_a_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v_ref_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3502_: u8 = 0;
    let mut v_kind_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3514_: u8 = 0;
    let mut v_kind_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prec_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhsPrec_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_val_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_val_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_catName_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v___x_3557_: u8 = 0;
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut v_p_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sep_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_psep_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3571_: u8 = 0;
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3584_: u8 = 0;
    let mut v_p_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sep_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_psep_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allowTrailingSep_3588_: u8 = 0;
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v_val_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asciiVal_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preserveForPP_3604_: u8 = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_3404_) {
                0 => {
                    lean_dec(v_a_3406_);
                    v_name_3408_ = lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3437_ = (!lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3437_ == 0 {
                        v___x_3410_ = v_x_3404_;
                        v_isShared_3411_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_name_3408_);
                        lean_dec(v_x_3404_);
                        v___x_3410_ = lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3437_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_name_3438_ = lean_ctor_get(v_x_3404_, 0);
                    v_p_3439_ = lean_ctor_get(v_x_3404_, 1);
                    v_isSharedCheck_3471_ = (!lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3471_ == 0 {
                        v___x_3441_ = v_x_3404_;
                        v_isShared_3442_ = v_isSharedCheck_3471_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_p_3439_);
                        lean_inc(v_name_3438_);
                        lean_dec(v_x_3404_);
                        v___x_3441_ = lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3471_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_name_3472_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc(v_name_3472_);
                    v_p_u2081_3473_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc_ref(v_p_u2081_3473_);
                    v_p_u2082_3474_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc_ref(v_p_u2082_3474_);
                    lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3475_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
                    v___x_3476_ = l_Lean_Parser_getBinaryAlias___redArg(v___x_3475_, v_name_3472_);
                    if lean_obj_tag(v___x_3476_) == 0 {
                        v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
                        lean_inc(v_a_3477_);
                        lean_dec_ref_known(v___x_3476_, 1);
                        lean_inc(v_a_3406_);
                        lean_inc_ref(v_a_3405_);
                        v___x_3478_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_p_u2081_3473_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if lean_obj_tag(v___x_3478_) == 0 {
                            v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
                            lean_inc(v_a_3479_);
                            lean_dec_ref_known(v___x_3478_, 1);
                            v___x_3480_ = lean_pretty_printer_formatter_interpret_parser_descr(
                                v_p_u2082_3474_,
                                v_a_3405_,
                                v_a_3406_,
                            );
                            if lean_obj_tag(v___x_3480_) == 0 {
                                v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
                                v_isSharedCheck_3489_ = (!lean_is_exclusive(v___x_3480_)) as u8;
                                if v_isSharedCheck_3489_ == 0 {
                                    v___x_3483_ = v___x_3480_;
                                    v_isShared_3484_ = v_isSharedCheck_3489_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_3481_);
                                    lean_dec(v___x_3480_);
                                    v___x_3483_ = lean_box(0);
                                    v_isShared_3484_ = v_isSharedCheck_3489_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3479_);
                                lean_dec(v_a_3477_);
                                return v___x_3480_;
                            }
                        } else {
                            lean_dec(v_a_3477_);
                            lean_dec_ref(v_p_u2082_3474_);
                            lean_dec(v_a_3406_);
                            lean_dec_ref(v_a_3405_);
                            return v___x_3478_;
                        }
                    } else {
                        lean_dec_ref(v_p_u2082_3474_);
                        lean_dec_ref(v_p_u2081_3473_);
                        lean_dec(v_a_3406_);
                        v_a_3490_ = lean_ctor_get(v___x_3476_, 0);
                        v_isSharedCheck_3502_ = (!lean_is_exclusive(v___x_3476_)) as u8;
                        if v_isSharedCheck_3502_ == 0 {
                            v___x_3492_ = v___x_3476_;
                            v_isShared_3493_ = v_isSharedCheck_3502_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3490_);
                            lean_dec(v___x_3476_);
                            v___x_3492_ = lean_box(0);
                            v_isShared_3493_ = v_isSharedCheck_3502_;
                            state = 15;
                            continue;
                        }
                    }
                }
                3 => {
                    v_kind_3503_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc(v_kind_3503_);
                    v_p_3504_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc_ref(v_p_3504_);
                    lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3505_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3504_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3505_) == 0 {
                        v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
                        v_isSharedCheck_3514_ = (!lean_is_exclusive(v___x_3505_)) as u8;
                        if v_isSharedCheck_3514_ == 0 {
                            v___x_3508_ = v___x_3505_;
                            v_isShared_3509_ = v_isSharedCheck_3514_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_3506_);
                            lean_dec(v___x_3505_);
                            v___x_3508_ = lean_box(0);
                            v_isShared_3509_ = v_isSharedCheck_3514_;
                            state = 17;
                            continue;
                        }
                    } else {
                        lean_dec(v_kind_3503_);
                        return v___x_3505_;
                    }
                }
                4 => {
                    v_kind_3515_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc(v_kind_3515_);
                    v_prec_3516_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc(v_prec_3516_);
                    v_lhsPrec_3517_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc(v_lhsPrec_3517_);
                    v_p_3518_ = lean_ctor_get(v_x_3404_, 3);
                    lean_inc_ref(v_p_3518_);
                    lean_dec_ref_known(v_x_3404_, 4);
                    v___x_3519_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3518_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3519_) == 0 {
                        v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
                        v_isSharedCheck_3528_ = (!lean_is_exclusive(v___x_3519_)) as u8;
                        if v_isSharedCheck_3528_ == 0 {
                            v___x_3522_ = v___x_3519_;
                            v_isShared_3523_ = v_isSharedCheck_3528_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_3520_);
                            lean_dec(v___x_3519_);
                            v___x_3522_ = lean_box(0);
                            v_isShared_3523_ = v_isSharedCheck_3528_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_dec(v_lhsPrec_3517_);
                        lean_dec(v_prec_3516_);
                        lean_dec(v_kind_3515_);
                        return v___x_3519_;
                    }
                }
                5 => {
                    lean_dec(v_a_3406_);
                    lean_dec_ref(v_a_3405_);
                    v_val_3529_ = lean_ctor_get(v_x_3404_, 0);
                    v_isSharedCheck_3537_ = (!lean_is_exclusive(v_x_3404_)) as u8;
                    if v_isSharedCheck_3537_ == 0 {
                        v___x_3531_ = v_x_3404_;
                        v_isShared_3532_ = v_isSharedCheck_3537_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_val_3529_);
                        lean_dec(v_x_3404_);
                        v___x_3531_ = lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3537_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    lean_dec(v_a_3406_);
                    lean_dec_ref(v_a_3405_);
                    v_val_3538_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc_ref(v_val_3538_);
                    lean_dec_ref_known(v_x_3404_, 1);
                    v___x_3539_ = 0;
                    v___x_3540_ = lean_box((v___x_3539_) as usize);
                    v___x_3541_ = lean_alloc_closure(
                        l_Lean_Parser_nonReservedSymbol_formatter___boxed as *mut core::ffi::c_void,
                        7,
                        2,
                    );
                    lean_closure_set(v___x_3541_, 0, v_val_3538_);
                    lean_closure_set(v___x_3541_, 1, v___x_3540_);
                    v___x_3542_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3542_, 0, v___x_3541_);
                    return v___x_3542_;
                }
                7 => {
                    lean_dec(v_a_3406_);
                    lean_dec_ref(v_a_3405_);
                    v_catName_3543_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc(v_catName_3543_);
                    lean_dec_ref_known(v_x_3404_, 2);
                    v___x_3544_ = lean_alloc_closure(
                        l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___boxed
                            as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    lean_closure_set(v___x_3544_, 0, v_catName_3543_);
                    v___x_3545_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3545_, 0, v___x_3544_);
                    return v___x_3545_;
                }
                8 => {
                    v_declName_3546_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc(v_declName_3546_);
                    lean_dec_ref_known(v_x_3404_, 1);
                    v___x_3547_ = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
                    v___x_3548_ = l_Lean_ParserCompiler_CombinatorAttribute_runDeclFor___redArg(
                        v___x_3547_,
                        v_declName_3546_,
                        v_a_3405_,
                        v_a_3406_,
                    );
                    lean_dec(v_a_3406_);
                    lean_dec_ref(v_a_3405_);
                    return v___x_3548_;
                }
                9 => {
                    v_name_3549_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc_ref(v_name_3549_);
                    v_kind_3550_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc(v_kind_3550_);
                    v_p_3551_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc_ref(v_p_3551_);
                    lean_dec_ref_known(v_x_3404_, 3);
                    v___x_3552_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3551_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3552_) == 0 {
                        v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
                        v_isSharedCheck_3567_ = (!lean_is_exclusive(v___x_3552_)) as u8;
                        if v_isSharedCheck_3567_ == 0 {
                            v___x_3555_ = v___x_3552_;
                            v_isShared_3556_ = v_isSharedCheck_3567_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3553_);
                            lean_dec(v___x_3552_);
                            v___x_3555_ = lean_box(0);
                            v_isShared_3556_ = v_isSharedCheck_3567_;
                            state = 23;
                            continue;
                        }
                    } else {
                        lean_dec(v_kind_3550_);
                        lean_dec_ref(v_name_3549_);
                        return v___x_3552_;
                    }
                }
                10 => {
                    v_p_3568_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc_ref(v_p_3568_);
                    v_sep_3569_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc_ref(v_sep_3569_);
                    v_psep_3570_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc_ref(v_psep_3570_);
                    v_allowTrailingSep_3571_ = lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref_known(v_x_3404_, 3);
                    lean_inc(v_a_3406_);
                    lean_inc_ref(v_a_3405_);
                    v___x_3572_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3568_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3572_) == 0 {
                        v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
                        lean_inc(v_a_3573_);
                        lean_dec_ref_known(v___x_3572_, 1);
                        v___x_3574_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_psep_3570_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if lean_obj_tag(v___x_3574_) == 0 {
                            v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
                            v_isSharedCheck_3584_ = (!lean_is_exclusive(v___x_3574_)) as u8;
                            if v_isSharedCheck_3584_ == 0 {
                                v___x_3577_ = v___x_3574_;
                                v_isShared_3578_ = v_isSharedCheck_3584_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3575_);
                                lean_dec(v___x_3574_);
                                v___x_3577_ = lean_box(0);
                                v_isShared_3578_ = v_isSharedCheck_3584_;
                                state = 25;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3573_);
                            lean_dec_ref(v_sep_3569_);
                            return v___x_3574_;
                        }
                    } else {
                        lean_dec_ref(v_psep_3570_);
                        lean_dec_ref(v_sep_3569_);
                        lean_dec(v_a_3406_);
                        lean_dec_ref(v_a_3405_);
                        return v___x_3572_;
                    }
                }
                11 => {
                    v_p_3585_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc_ref(v_p_3585_);
                    v_sep_3586_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc_ref(v_sep_3586_);
                    v_psep_3587_ = lean_ctor_get(v_x_3404_, 2);
                    lean_inc_ref(v_psep_3587_);
                    v_allowTrailingSep_3588_ = lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec_ref_known(v_x_3404_, 3);
                    lean_inc(v_a_3406_);
                    lean_inc_ref(v_a_3405_);
                    v___x_3589_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3585_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3589_) == 0 {
                        v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
                        lean_inc(v_a_3590_);
                        lean_dec_ref_known(v___x_3589_, 1);
                        v___x_3591_ = lean_pretty_printer_formatter_interpret_parser_descr(
                            v_psep_3587_,
                            v_a_3405_,
                            v_a_3406_,
                        );
                        if lean_obj_tag(v___x_3591_) == 0 {
                            v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
                            v_isSharedCheck_3601_ = (!lean_is_exclusive(v___x_3591_)) as u8;
                            if v_isSharedCheck_3601_ == 0 {
                                v___x_3594_ = v___x_3591_;
                                v_isShared_3595_ = v_isSharedCheck_3601_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_3592_);
                                lean_dec(v___x_3591_);
                                v___x_3594_ = lean_box(0);
                                v_isShared_3595_ = v_isSharedCheck_3601_;
                                state = 27;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3590_);
                            lean_dec_ref(v_sep_3586_);
                            return v___x_3591_;
                        }
                    } else {
                        lean_dec_ref(v_psep_3587_);
                        lean_dec_ref(v_sep_3586_);
                        lean_dec(v_a_3406_);
                        lean_dec_ref(v_a_3405_);
                        return v___x_3589_;
                    }
                }
                _ => {
                    lean_dec(v_a_3406_);
                    lean_dec_ref(v_a_3405_);
                    v_val_3602_ = lean_ctor_get(v_x_3404_, 0);
                    lean_inc_ref(v_val_3602_);
                    v_asciiVal_3603_ = lean_ctor_get(v_x_3404_, 1);
                    lean_inc_ref(v_asciiVal_3603_);
                    v_preserveForPP_3604_ = lean_ctor_get_uint8(
                        v_x_3404_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec_ref_known(v_x_3404_, 2);
                    v___x_3605_ = lean_box((v_preserveForPP_3604_) as usize);
                    v___x_3606_ = lean_alloc_closure(
                        l_Lean_Parser_unicodeSymbol_formatter___boxed as *mut core::ffi::c_void,
                        8,
                        3,
                    );
                    lean_closure_set(v___x_3606_, 0, v_val_3602_);
                    lean_closure_set(v___x_3606_, 1, v_asciiVal_3603_);
                    lean_closure_set(v___x_3606_, 2, v___x_3605_);
                    v___x_3607_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3607_, 0, v___x_3606_);
                    return v___x_3607_;
                }
            },
            1 => {
                v___x_3412_ = l_Lean_PrettyPrinter_Formatter_formatterAliasesRef;
                v___x_3413_ = l_Lean_Parser_getConstAlias___redArg(v___x_3412_, v_name_3408_);
                if lean_obj_tag(v___x_3413_) == 0 {
                    lean_del_object(v___x_3410_);
                    lean_dec_ref(v_a_3405_);
                    v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
                    v_isSharedCheck_3421_ = (!lean_is_exclusive(v___x_3413_)) as u8;
                    if v_isSharedCheck_3421_ == 0 {
                        v___x_3416_ = v___x_3413_;
                        v_isShared_3417_ = v_isSharedCheck_3421_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3414_);
                        lean_dec(v___x_3413_);
                        v___x_3416_ = lean_box(0);
                        v_isShared_3417_ = v_isSharedCheck_3421_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3422_ = lean_ctor_get(v___x_3413_, 0);
                    v_isSharedCheck_3436_ = (!lean_is_exclusive(v___x_3413_)) as u8;
                    if v_isSharedCheck_3436_ == 0 {
                        v___x_3424_ = v___x_3413_;
                        v_isShared_3425_ = v_isSharedCheck_3436_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3422_);
                        lean_dec(v___x_3413_);
                        v___x_3424_ = lean_box(0);
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
                    v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
                    v___x_3419_ = v_reuseFailAlloc_3420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3419_;
            }
            4 => {
                v_ref_3426_ = lean_ctor_get(v_a_3405_, 5);
                lean_inc(v_ref_3426_);
                lean_dec_ref(v_a_3405_);
                v___x_3427_ = lean_io_error_to_string(v_a_3422_);
                if v_isShared_3411_ == 0 {
                    lean_ctor_set_tag(v___x_3410_, 3);
                    lean_ctor_set(v___x_3410_, 0, v___x_3427_);
                    v___x_3429_ = v___x_3410_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3427_);
                    v___x_3429_ = v_reuseFailAlloc_3435_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3430_ = l_Lean_MessageData_ofFormat(v___x_3429_);
                v___x_3431_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3431_, 0, v_ref_3426_);
                lean_ctor_set(v___x_3431_, 1, v___x_3430_);
                if v_isShared_3425_ == 0 {
                    lean_ctor_set(v___x_3424_, 0, v___x_3431_);
                    v___x_3433_ = v___x_3424_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
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
                if lean_obj_tag(v___x_3444_) == 0 {
                    lean_del_object(v___x_3441_);
                    v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
                    lean_inc(v_a_3445_);
                    lean_dec_ref_known(v___x_3444_, 1);
                    v___x_3446_ = lean_pretty_printer_formatter_interpret_parser_descr(
                        v_p_3439_, v_a_3405_, v_a_3406_,
                    );
                    if lean_obj_tag(v___x_3446_) == 0 {
                        v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
                        v_isSharedCheck_3455_ = (!lean_is_exclusive(v___x_3446_)) as u8;
                        if v_isSharedCheck_3455_ == 0 {
                            v___x_3449_ = v___x_3446_;
                            v_isShared_3450_ = v_isSharedCheck_3455_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3447_);
                            lean_dec(v___x_3446_);
                            v___x_3449_ = lean_box(0);
                            v_isShared_3450_ = v_isSharedCheck_3455_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3445_);
                        return v___x_3446_;
                    }
                } else {
                    lean_dec_ref(v_p_3439_);
                    lean_dec(v_a_3406_);
                    v_a_3456_ = lean_ctor_get(v___x_3444_, 0);
                    v_isSharedCheck_3470_ = (!lean_is_exclusive(v___x_3444_)) as u8;
                    if v_isSharedCheck_3470_ == 0 {
                        v___x_3458_ = v___x_3444_;
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3456_);
                        lean_dec(v___x_3444_);
                        v___x_3458_ = lean_box(0);
                        v_isShared_3459_ = v_isSharedCheck_3470_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3451_ = lean_apply_1(v_a_3445_, v_a_3447_);
                if v_isShared_3450_ == 0 {
                    lean_ctor_set(v___x_3449_, 0, v___x_3451_);
                    v___x_3453_ = v___x_3449_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3451_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3453_;
            }
            10 => {
                v_ref_3460_ = lean_ctor_get(v_a_3405_, 5);
                lean_inc(v_ref_3460_);
                lean_dec_ref(v_a_3405_);
                v___x_3461_ = lean_io_error_to_string(v_a_3456_);
                v___x_3462_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3462_, 0, v___x_3461_);
                v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
                if v_isShared_3442_ == 0 {
                    lean_ctor_set_tag(v___x_3441_, 0);
                    lean_ctor_set(v___x_3441_, 1, v___x_3463_);
                    lean_ctor_set(v___x_3441_, 0, v_ref_3460_);
                    v___x_3465_ = v___x_3441_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_ref_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 1, v___x_3463_);
                    v___x_3465_ = v_reuseFailAlloc_3469_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3459_ == 0 {
                    lean_ctor_set(v___x_3458_, 0, v___x_3465_);
                    v___x_3467_ = v___x_3458_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3467_;
            }
            13 => {
                v___x_3485_ = lean_apply_2(v_a_3477_, v_a_3479_, v_a_3481_);
                if v_isShared_3484_ == 0 {
                    lean_ctor_set(v___x_3483_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3483_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3487_;
            }
            15 => {
                v_ref_3494_ = lean_ctor_get(v_a_3405_, 5);
                lean_inc(v_ref_3494_);
                lean_dec_ref(v_a_3405_);
                v___x_3495_ = lean_io_error_to_string(v_a_3490_);
                v___x_3496_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3496_, 0, v___x_3495_);
                v___x_3497_ = l_Lean_MessageData_ofFormat(v___x_3496_);
                v___x_3498_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3498_, 0, v_ref_3494_);
                lean_ctor_set(v___x_3498_, 1, v___x_3497_);
                if v_isShared_3493_ == 0 {
                    lean_ctor_set(v___x_3492_, 0, v___x_3498_);
                    v___x_3500_ = v___x_3492_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
                    v___x_3500_ = v_reuseFailAlloc_3501_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3500_;
            }
            17 => {
                v___x_3510_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_3510_, 0, v_kind_3503_);
                lean_closure_set(v___x_3510_, 1, v_a_3506_);
                if v_isShared_3509_ == 0 {
                    lean_ctor_set(v___x_3508_, 0, v___x_3510_);
                    v___x_3512_ = v___x_3508_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3513_, 0, v___x_3510_);
                    v___x_3512_ = v_reuseFailAlloc_3513_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3512_;
            }
            19 => {
                v___x_3524_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3524_, 0, v_kind_3515_);
                lean_closure_set(v___x_3524_, 1, v_prec_3516_);
                lean_closure_set(v___x_3524_, 2, v_lhsPrec_3517_);
                lean_closure_set(v___x_3524_, 3, v_a_3520_);
                if v_isShared_3523_ == 0 {
                    lean_ctor_set(v___x_3522_, 0, v___x_3524_);
                    v___x_3526_ = v___x_3522_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
                    v___x_3526_ = v_reuseFailAlloc_3527_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3526_;
            }
            21 => {
                v___x_3533_ = lean_alloc_closure(
                    l_Lean_Parser_symbol_formatter___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___x_3533_, 0, v_val_3529_);
                if v_isShared_3532_ == 0 {
                    lean_ctor_set_tag(v___x_3531_, 0);
                    lean_ctor_set(v___x_3531_, 0, v___x_3533_);
                    v___x_3535_ = v___x_3531_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3536_, 0, v___x_3533_);
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
                v___x_3559_ = lean_box((v___x_3557_) as usize);
                v___x_3560_ = lean_box((v___x_3558_) as usize);
                lean_inc(v_kind_3550_);
                v___x_3561_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_mkAntiquot_formatter_x27___boxed
                        as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3561_, 0, v_name_3549_);
                lean_closure_set(v___x_3561_, 1, v_kind_3550_);
                lean_closure_set(v___x_3561_, 2, v___x_3559_);
                lean_closure_set(v___x_3561_, 3, v___x_3560_);
                v___x_3562_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_node_formatter___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___x_3562_, 0, v_kind_3550_);
                lean_closure_set(v___x_3562_, 1, v_a_3553_);
                v___f_3563_ = lean_alloc_closure(
                    l_Lean_PrettyPrinter_Formatter_interpretParserDescr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_3563_, 0, v___x_3561_);
                lean_closure_set(v___f_3563_, 1, v___x_3562_);
                if v_isShared_3556_ == 0 {
                    lean_ctor_set(v___x_3555_, 0, v___f_3563_);
                    v___x_3565_ = v___x_3555_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___f_3563_);
                    v___x_3565_ = v_reuseFailAlloc_3566_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3565_;
            }
            25 => {
                v___x_3579_ = lean_box((v_allowTrailingSep_3571_) as usize);
                v___x_3580_ = lean_alloc_closure(
                    l_Lean_Parser_sepBy_formatter___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3580_, 0, v_a_3573_);
                lean_closure_set(v___x_3580_, 1, v_sep_3569_);
                lean_closure_set(v___x_3580_, 2, v_a_3575_);
                lean_closure_set(v___x_3580_, 3, v___x_3579_);
                if v_isShared_3578_ == 0 {
                    lean_ctor_set(v___x_3577_, 0, v___x_3580_);
                    v___x_3582_ = v___x_3577_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3582_;
            }
            27 => {
                v___x_3596_ = lean_box((v_allowTrailingSep_3588_) as usize);
                v___x_3597_ = lean_alloc_closure(
                    l_Lean_Parser_sepBy1_formatter___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                lean_closure_set(v___x_3597_, 0, v_a_3590_);
                lean_closure_set(v___x_3597_, 1, v_sep_3586_);
                lean_closure_set(v___x_3597_, 2, v_a_3592_);
                lean_closure_set(v___x_3597_, 3, v___x_3596_);
                if v_isShared_3595_ == 0 {
                    lean_ctor_set(v___x_3594_, 0, v___x_3597_);
                    v___x_3599_ = v___x_3594_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
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
    mut v_x_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3612_: *mut LeanObject = core::ptr::null_mut();
    v_res_3612_ =
        lean_pretty_printer_formatter_interpret_parser_descr(v_x_3608_, v_a_3609_, v_a_3610_);
    return v_res_3612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_Parser_initFn_00___x40_Lean_Parser_1428529586____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_ident_parenthesizer__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_numLit_parenthesizer__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_scientificLit_parenthesizer__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_charLit_parenthesizer__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer___regBuiltin_Lean_PrettyPrinter_Parenthesizer_strLit_parenthesizer__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_ident_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_ident_formatter__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_numLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_numLit_formatter__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_scientificLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_scientificLit_formatter__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_charLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_charLit_formatter__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_0__Lean_PrettyPrinter_Formatter_strLit_formatter___regBuiltin_Lean_PrettyPrinter_Formatter_strLit_formatter__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Module(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser(builtin);
}
