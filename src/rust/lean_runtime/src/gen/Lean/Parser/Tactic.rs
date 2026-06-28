// Lean compiler output
// Module: Lean.Parser.Tactic
// Imports: Lean.Parser.Term Lean.Parser.Tactic.Doc Std.Tactic.Do.Syntax
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_errorAtSavedPos, l_Lean_Parser_leadingNode,
    l_Lean_Parser_mkAntiquot, l_Lean_Parser_nonReservedSymbol, l_Lean_Parser_orelse,
    l_Lean_Parser_sepBy1, l_Lean_Parser_symbol, l_Lean_Parser_withAntiquot,
    l_Lean_Parser_withPosition,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_addBuiltinLeadingParser, l_Lean_Parser_registerAlias,
};
use crate::r#gen::Lean::Parser::Extra::{
    l_Lean_Parser_ident, l_Lean_Parser_ident_formatter___boxed,
    l_Lean_Parser_ident_parenthesizer___boxed, l_Lean_Parser_leadingNode_formatter___boxed,
    l_Lean_Parser_mkAntiquot_formatter___boxed, l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_nonReservedSymbol_formatter___boxed,
    l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, l_Lean_Parser_optional,
    l_Lean_Parser_optional_formatter___boxed, l_Lean_Parser_optional_parenthesizer___boxed,
    l_Lean_Parser_ppDedent_parenthesizer___boxed, l_Lean_Parser_sepBy1_formatter___boxed,
    l_Lean_Parser_sepBy1_parenthesizer___boxed, l_Lean_Parser_symbol_formatter___boxed,
    l_Lean_Parser_symbol_parenthesizer___boxed, l_Lean_Parser_withPosition_formatter___boxed,
    l_Lean_ppDedent_formatter___boxed,
};
use crate::r#gen::Lean::Parser::Tactic::Doc::{
    initialize_Lean_Parser_Tactic_Doc, runtime_initialize_Lean_Parser_Tactic_Doc,
};
use crate::r#gen::Lean::Parser::Term::Basic::{
    l_Lean_Parser_Tactic_tacticSeq, l_Lean_Parser_Tactic_tacticSeq_formatter___boxed,
    l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed, l_Lean_Parser_Tactic_tacticSeqBracketed,
    l_Lean_Parser_Tactic_tacticSeqBracketed_formatter,
    l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer, l_Lean_Parser_Tactic_tacticSeqIndentGt,
    l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed,
    l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed, l_Lean_Parser_Term_hole,
    l_Lean_Parser_Term_hole_formatter___boxed, l_Lean_Parser_Term_hole_parenthesizer___boxed,
    l_Lean_Parser_Term_syntheticHole, l_Lean_Parser_Term_syntheticHole_formatter___boxed,
    l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed,
};
use crate::r#gen::Lean::Parser::Term::{
    initialize_Lean_Parser_Term, l_Lean_Parser_Term_generalizingParam,
    l_Lean_Parser_Term_generalizingParam_formatter___boxed,
    l_Lean_Parser_Term_generalizingParam_parenthesizer___boxed, l_Lean_Parser_Term_matchAlts,
    l_Lean_Parser_Term_matchAlts_formatter, l_Lean_Parser_Term_matchAlts_parenthesizer,
    l_Lean_Parser_Term_matchDiscr, l_Lean_Parser_Term_matchDiscr_formatter___boxed,
    l_Lean_Parser_Term_matchDiscr_parenthesizer___boxed, l_Lean_Parser_Term_motive,
    l_Lean_Parser_Term_motive_formatter___boxed, l_Lean_Parser_Term_motive_parenthesizer___boxed,
    runtime_initialize_Lean_Parser_Term,
};
use crate::r#gen::Lean::Parser::Types::{l_Lean_Parser_leadPrec, l_Lean_Parser_withCache};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_registerAlias, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_registerAlias,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11103865283154438669 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__8_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 73, 110, 100, 101, 110, 116, 71, 116, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,1281033301621628941 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__10_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,15632569633373612756 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Tactic_tacticSeqIndentGt_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__15_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Tactic_tacticSeqIndentGt_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__17_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Tactic_tacticSeq_formatter___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Parser_Tactic_tacticSeq_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown___closed__0_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [117, 110, 107, 110, 111, 119, 110, 0],
};
static mut l_Lean_Parser_Tactic_unknown___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_unknown___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_unknown___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_unknown___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_unknown___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject,
        9908055704337889844 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_unknown___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_unknown___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_unknown___closed__3_value: LeanStringObject<15> =
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
            117, 110, 107, 110, 111, 119, 110, 32, 116, 97, 99, 116, 105, 99, 0,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_unknown___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_unknown___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_unknown___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_unknown___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_unknown___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_unknown___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_unknown___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_unknown: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__0_value) as *mut LeanObject,16145843736367156323 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__0_value) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__1_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__3_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__4_value) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_ident_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_errorAtSavedPos_formatter___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__3_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_withPosition_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_formatter___closed__5_value: LeanClosureObject<3> =
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
        m_fun: l_Lean_Parser_leadingNode_formatter___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_formatter___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject,9908055704337889844 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value) as *mut LeanObject,15122430186075801277 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_ident_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_errorAtSavedPos_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__3_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_withPosition_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5_value: LeanClosureObject<3> =
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
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 3,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_unknown___closed__0_value) as *mut LeanObject,9908055704337889844 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value) as *mut LeanObject,16315037717850850505 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Parser_Tactic_nestedTactic: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 101, 115, 116, 101, 100, 84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__0_value) as *mut LeanObject,7240493354055247409 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__0_value) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__1_value) as *mut LeanObject,((( 63 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 41 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__3_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__4_value) as *mut LeanObject,((( 41 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_matchRhs___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_matchRhs___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_matchRhs___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_matchRhs___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_matchRhs: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_matchAlts___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_matchAlts___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_matchAlts: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_match___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Parser_Tactic_match___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_match___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_match___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_match___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_match___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject,
        15889294097160086760 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_match___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_match___closed__3_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [109, 97, 116, 99, 104, 32, 0],
};
static mut l_Lean_Parser_Tactic_match___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_match___closed__7_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Parser_Tactic_match___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__7_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_match___closed__10_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [32, 119, 105, 116, 104, 32, 0],
};
static mut l_Lean_Parser_Tactic_match___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__10_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__18: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_match: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0_value: LeanStringObject<399> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 399, m_capacity: 399, m_length: 398, m_data: [96, 109, 97, 116, 99, 104, 96, 32, 112, 101, 114, 102, 111, 114, 109, 115, 32, 99, 97, 115, 101, 32, 97, 110, 97, 108, 121, 115, 105, 115, 32, 111, 110, 32, 111, 110, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 46, 10, 83, 101, 101, 32, 91, 73, 110, 100, 117, 99, 116, 105, 111, 110, 32, 97, 110, 100, 32, 82, 101, 99, 117, 114, 115, 105, 111, 110, 93, 91, 116, 112, 105, 108, 52, 93, 46, 10, 84, 104, 101, 32, 115, 121, 110, 116, 97, 120, 32, 102, 111, 114, 32, 116, 104, 101, 32, 96, 109, 97, 116, 99, 104, 96, 32, 116, 97, 99, 116, 105, 99, 32, 105, 115, 32, 116, 104, 101, 32, 115, 97, 109, 101, 32, 97, 115, 32, 116, 101, 114, 109, 45, 109, 111, 100, 101, 32, 96, 109, 97, 116, 99, 104, 96, 44, 32, 101, 120, 99, 101, 112, 116, 32, 116, 104, 97, 116, 10, 116, 104, 101, 32, 109, 97, 116, 99, 104, 32, 97, 114, 109, 115, 32, 97, 114, 101, 32, 116, 97, 99, 116, 105, 99, 115, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 46, 10, 96, 96, 96, 10, 101, 120, 97, 109, 112, 108, 101, 32, 40, 110, 32, 58, 32, 78, 97, 116, 41, 32, 58, 32, 110, 32, 61, 32, 110, 32, 58, 61, 32, 98, 121, 10, 32, 32, 109, 97, 116, 99, 104, 32, 110, 32, 119, 105, 116, 104, 10, 32, 32, 124, 32, 48, 32, 61, 62, 32, 114, 102, 108, 10, 32, 32, 124, 32, 105, 43, 49, 32, 61, 62, 32, 115, 105, 109, 112, 10, 96, 96, 96, 10, 10, 91, 116, 112, 105, 108, 52, 93, 58, 32, 104, 116, 116, 112, 115, 58, 47, 47, 108, 101, 97, 110, 45, 108, 97, 110, 103, 46, 111, 114, 103, 47, 116, 104, 101, 111, 114, 101, 109, 95, 112, 114, 111, 118, 105, 110, 103, 95, 105, 110, 95, 108, 101, 97, 110, 52, 47, 105, 110, 100, 117, 99, 116, 105, 111, 110, 95, 97, 110, 100, 95, 114, 101, 99, 117, 114, 115, 105, 111, 110, 46, 104, 116, 109, 108, 10, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 48 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__0_value) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__1_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__3_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__4_value) as *mut LeanObject,((( 36 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_formatter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_hole_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_matchRhs_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_syntheticHole_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_matchRhs_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_formatter___closed__2_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_formatter___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__19_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_matchRhs_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_generalizingParam_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_motive_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__5_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_optional_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_matchDiscr_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__7_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__8_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_sepBy1_formatter___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__7_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__8_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_formatter___closed__9_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__10_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_formatter___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_formatter___closed__9_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match_formatter___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_formatter___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_match_formatter___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject,15889294097160086760 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value) as *mut LeanObject,7310831296212205177 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_hole_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_syntheticHole_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__21_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_generalizingParam_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_motive_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__5_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_optional_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Term_matchDiscr_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__8_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_sepBy1_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__7_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__7_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_match_parenthesizer___closed__9_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_symbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__10_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_match_parenthesizer___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_match_parenthesizer___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_match___closed__0_value) as *mut LeanObject,15889294097160086760 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value) as *mut LeanObject,13693333671287639981 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_introMatch___closed__0_value: LeanStringObject<11> =
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
        m_data: [105, 110, 116, 114, 111, 77, 97, 116, 99, 104, 0],
    };
static mut l_Lean_Parser_Tactic_introMatch___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Parser_Tactic_introMatch___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value) as *mut LeanObject,
        12010019835345775192 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Tactic_introMatch___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_introMatch___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Tactic_introMatch___closed__3_value: LeanStringObject<6> =
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
static mut l_Lean_Parser_Tactic_introMatch___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Tactic_introMatch___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Tactic_introMatch___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Tactic_introMatch: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 67 as usize) << 1) | 1) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__0_value) as *mut LeanObject,((( 25 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__1_value) as *mut LeanObject,((( 40 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 67 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 67 as usize) << 1) | 1) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__3_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__4_value) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_introMatch_formatter___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
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
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_introMatch_formatter___closed__1_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_nonReservedSymbol_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__3_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch_formatter___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_introMatch_formatter___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value) as *mut LeanObject,12010019835345775192 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__0_value) as *mut LeanObject,10270598561614596169 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_mkAntiquot_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 4,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__3_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Tactic_introMatch___closed__0_value) as *mut LeanObject,12010019835345775192 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__0_value) as *mut LeanObject,9478236248997585725 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [109, 97, 116, 99, 104, 82, 104, 115, 84, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__0_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject,6123326918764794581 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 82, 104, 115, 0]};
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__2_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject,13478968759552966442 as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Lean_Parser_Tactic_tacticSeq;
    v___x_840_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_840_, 0, v___x_839_);
    return v___x_840_;
}
pub unsafe fn _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = l_Lean_Parser_Tactic_tacticSeqIndentGt;
    v___x_858_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_858_, 0, v___x_857_);
    return v___x_858_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_874_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                v___x_875_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                v___x_876_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
                v___x_877_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                v___x_878_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                v___x_890_ = l_Lean_Parser_registerAlias(
                    v___x_874_, v___x_875_, v___x_876_, v___x_877_, v___x_878_,
                );
                if lean_obj_tag(v___x_890_) == 0 {
                    lean_dec_ref_known(v___x_890_, 1);
                    v___x_891_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__20_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                    v___x_892_ =
                        l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_874_, v___x_891_);
                    if lean_obj_tag(v___x_892_) == 0 {
                        lean_dec_ref_known(v___x_892_, 1);
                        v___x_893_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__22_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                        v___x_894_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                            v___x_874_, v___x_893_,
                        );
                        v___y_880_ = v___x_894_;
                        state = 1;
                        continue;
                    } else {
                        v___y_880_ = v___x_892_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_880_ = v___x_890_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_880_) == 0 {
                    lean_dec_ref_known(v___y_880_, 1);
                    v___x_881_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__11_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                    v___x_882_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__12_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                    v___x_883_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__13_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_);
                    v___x_884_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__14_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                    v___x_885_ = l_Lean_Parser_registerAlias(
                        v___x_881_, v___x_882_, v___x_883_, v___x_884_, v___x_878_,
                    );
                    if lean_obj_tag(v___x_885_) == 0 {
                        lean_dec_ref_known(v___x_885_, 1);
                        v___x_886_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__16_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                        v___x_887_ =
                            l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_881_, v___x_886_);
                        if lean_obj_tag(v___x_887_) == 0 {
                            lean_dec_ref_known(v___x_887_, 1);
                            v___x_888_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__18_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
                            v___x_889_ = l_Lean_PrettyPrinter_Parenthesizer_registerAlias(
                                v___x_881_, v___x_888_,
                            );
                            return v___x_889_;
                        } else {
                            return v___x_887_;
                        }
                    } else {
                        return v___x_885_;
                    }
                } else {
                    return v___y_880_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2____boxed(
    mut v_a_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_896_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
    return v_res_896_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__2() -> *mut LeanObject {
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: u8 = 0;
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    v___x_903_ = 0;
    v___x_904_ = 1;
    v___x_905_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_906_ = l_Lean_Parser_Tactic_unknown___closed__0;
    v___x_907_ = l_Lean_Parser_mkAntiquot(v___x_906_, v___x_905_, v___x_904_, v___x_903_);
    return v___x_907_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__4() -> *mut LeanObject {
    let mut v___x_909_: u8 = 0;
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = 1;
    v___x_910_ = l_Lean_Parser_Tactic_unknown___closed__3;
    v___x_911_ = l_Lean_Parser_errorAtSavedPos(v___x_910_, v___x_909_);
    return v___x_911_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__5() -> *mut LeanObject {
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__4_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__4,
    );
    v___x_913_ = l_Lean_Parser_ident;
    v___x_914_ = l_Lean_Parser_andthen(v___x_913_, v___x_912_);
    return v___x_914_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__6() -> *mut LeanObject {
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__5_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__5,
    );
    v___x_916_ = l_Lean_Parser_withPosition(v___x_915_);
    return v___x_916_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__7() -> *mut LeanObject {
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___x_917_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__6_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__6,
    );
    v___x_918_ = lean_unsigned_to_nat(1024);
    v___x_919_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_920_ = l_Lean_Parser_leadingNode(v___x_919_, v___x_918_, v___x_917_);
    return v___x_920_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__8() -> *mut LeanObject {
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__7_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__7,
    );
    v___x_922_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__2_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__2,
    );
    v___x_923_ = l_Lean_Parser_withAntiquot(v___x_922_, v___x_921_);
    return v___x_923_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown___closed__9() -> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__8_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__8,
    );
    v___x_925_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_926_ = l_Lean_Parser_withCache(v___x_925_, v___x_924_);
    return v___x_926_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_unknown() -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_unknown___closed__9_once),
        _init_l_Lean_Parser_Tactic_unknown___closed__9,
    );
    return v___x_927_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1()
-> *mut LeanObject {
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1;
    v___x_933_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_934_ = l_Lean_Parser_Tactic_unknown;
    v___x_935_ = lean_unsigned_to_nat(1000);
    v___x_936_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_932_, v___x_933_, v___x_934_, v___x_935_);
    return v___x_936_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___boxed(
    mut v_a_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_938_: *mut LeanObject = core::ptr::null_mut();
    v_res_938_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
    return v_res_938_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3()
-> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_966_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___closed__6;
    v___x_967_ = l_Lean_addBuiltinDeclarationRanges(v___x_965_, v___x_966_);
    return v___x_967_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3___boxed(
    mut v_a_968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_969_: *mut LeanObject = core::ptr::null_mut();
    v_res_969_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
    return v_res_969_;
}
pub unsafe fn l_Lean_Parser_Tactic_unknown_formatter(
    mut v_a_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
    mut v_a_993_: *mut LeanObject,
    mut v_a_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    v___x_996_ = l_Lean_Parser_Tactic_unknown_formatter___closed__0;
    v___x_997_ = l_Lean_Parser_Tactic_unknown_formatter___closed__5;
    v___x_998_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_996_, v___x_997_, v_a_991_, v_a_992_, v_a_993_, v_a_994_,
    );
    return v___x_998_;
}
pub unsafe fn l_Lean_Parser_Tactic_unknown_formatter___boxed(
    mut v_a_999_: *mut LeanObject,
    mut v_a_1000_: *mut LeanObject,
    mut v_a_1001_: *mut LeanObject,
    mut v_a_1002_: *mut LeanObject,
    mut v_a_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_res_1004_ = l_Lean_Parser_Tactic_unknown_formatter(v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
    lean_dec(v_a_1002_);
    lean_dec_ref(v_a_1001_);
    lean_dec(v_a_1000_);
    lean_dec_ref(v_a_999_);
    return v_res_1004_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7()
-> *mut LeanObject {
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1014_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_1015_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___closed__1;
    v___x_1016_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_unknown_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1017_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1013_,
        v___x_1014_,
        v___x_1015_,
        v___x_1016_,
    );
    return v___x_1017_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7___boxed(
    mut v_a_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
    return v_res_1019_;
}
pub unsafe fn l_Lean_Parser_Tactic_unknown_parenthesizer(
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
    mut v_a_1043_: *mut LeanObject,
    mut v_a_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__0;
    v___x_1047_ = l_Lean_Parser_Tactic_unknown_parenthesizer___closed__5;
    v___x_1048_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1046_,
        v___x_1047_,
        v_a_1041_,
        v_a_1042_,
        v_a_1043_,
        v_a_1044_,
    );
    return v___x_1048_;
}
pub unsafe fn l_Lean_Parser_Tactic_unknown_parenthesizer___boxed(
    mut v_a_1049_: *mut LeanObject,
    mut v_a_1050_: *mut LeanObject,
    mut v_a_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_a_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ =
        l_Lean_Parser_Tactic_unknown_parenthesizer(v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
    lean_dec(v_a_1052_);
    lean_dec_ref(v_a_1051_);
    lean_dec(v_a_1050_);
    lean_dec_ref(v_a_1049_);
    return v_res_1054_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1064_ = l_Lean_Parser_Tactic_unknown___closed__1;
    v___x_1065_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___closed__1;
    v___x_1066_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_unknown_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1067_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1063_,
        v___x_1064_,
        v___x_1065_,
        v___x_1066_,
    );
    return v___x_1067_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11___boxed(
    mut v_a_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1069_: *mut LeanObject = core::ptr::null_mut();
    v_res_1069_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
    return v_res_1069_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_nestedTactic() -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
    return v___x_1070_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1()
-> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v___x_1078_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1;
    v___x_1079_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1;
    v___x_1080_ = l_Lean_Parser_Tactic_tacticSeqBracketed;
    v___x_1081_ = lean_unsigned_to_nat(1000);
    v___x_1082_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1078_, v___x_1079_, v___x_1080_, v___x_1081_);
    return v___x_1082_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___boxed(
    mut v_a_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1084_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
    return v_res_1084_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3()
-> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v___x_1111_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1___closed__1;
    v___x_1112_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___closed__6;
    v___x_1113_ = l_Lean_addBuiltinDeclarationRanges(v___x_1111_, v___x_1112_);
    return v___x_1113_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3___boxed(
    mut v_a_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v_res_1115_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
    return v_res_1115_;
}
pub unsafe fn l_Lean_Parser_Tactic_nestedTactic_formatter(
    mut v_a_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ = l_Lean_Parser_Tactic_tacticSeqBracketed_formatter(
        v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_,
    );
    return v___x_1121_;
}
pub unsafe fn l_Lean_Parser_Tactic_nestedTactic_formatter___boxed(
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1127_: *mut LeanObject = core::ptr::null_mut();
    v_res_1127_ =
        l_Lean_Parser_Tactic_nestedTactic_formatter(v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
    lean_dec(v_a_1125_);
    lean_dec_ref(v_a_1124_);
    lean_dec(v_a_1123_);
    lean_dec_ref(v_a_1122_);
    return v_res_1127_;
}
pub unsafe fn l_Lean_Parser_Tactic_nestedTactic_parenthesizer(
    mut v_a_1128_: *mut LeanObject,
    mut v_a_1129_: *mut LeanObject,
    mut v_a_1130_: *mut LeanObject,
    mut v_a_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_Parser_Tactic_tacticSeqBracketed_parenthesizer(
        v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_,
    );
    return v___x_1133_;
}
pub unsafe fn l_Lean_Parser_Tactic_nestedTactic_parenthesizer___boxed(
    mut v_a_1134_: *mut LeanObject,
    mut v_a_1135_: *mut LeanObject,
    mut v_a_1136_: *mut LeanObject,
    mut v_a_1137_: *mut LeanObject,
    mut v_a_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1139_: *mut LeanObject = core::ptr::null_mut();
    v_res_1139_ =
        l_Lean_Parser_Tactic_nestedTactic_parenthesizer(v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_);
    lean_dec(v_a_1137_);
    lean_dec_ref(v_a_1136_);
    lean_dec(v_a_1135_);
    lean_dec_ref(v_a_1134_);
    return v_res_1139_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_matchRhs___closed__0() -> *mut LeanObject {
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_Lean_Parser_Tactic_tacticSeq;
    v___x_1141_ = l_Lean_Parser_Term_syntheticHole;
    v___x_1142_ = l_Lean_Parser_orelse(v___x_1141_, v___x_1140_);
    return v___x_1142_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_matchRhs___closed__1() -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchRhs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchRhs___closed__0_once),
        _init_l_Lean_Parser_Tactic_matchRhs___closed__0,
    );
    v___x_1144_ = l_Lean_Parser_Term_hole;
    v___x_1145_ = l_Lean_Parser_orelse(v___x_1144_, v___x_1143_);
    return v___x_1145_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_matchRhs() -> *mut LeanObject {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1146_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchRhs___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchRhs___closed__1_once),
        _init_l_Lean_Parser_Tactic_matchRhs___closed__1,
    );
    return v___x_1146_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_matchAlts___closed__0() -> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1147_ = l_Lean_Parser_Tactic_matchRhs;
    v___x_1148_ = l_Lean_Parser_Term_matchAlts(v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_matchAlts() -> *mut LeanObject {
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    v___x_1149_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchAlts___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_matchAlts___closed__0_once),
        _init_l_Lean_Parser_Tactic_matchAlts___closed__0,
    );
    return v___x_1149_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__2() -> *mut LeanObject {
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = 0;
    v___x_1157_ = 1;
    v___x_1158_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1159_ = l_Lean_Parser_Tactic_match___closed__0;
    v___x_1160_ = l_Lean_Parser_mkAntiquot(v___x_1159_, v___x_1158_, v___x_1157_, v___x_1156_);
    return v___x_1160_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__4() -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = l_Lean_Parser_Tactic_match___closed__3;
    v___x_1163_ = l_Lean_Parser_symbol(v___x_1162_);
    return v___x_1163_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__5() -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Lean_Parser_Term_generalizingParam;
    v___x_1165_ = l_Lean_Parser_optional(v___x_1164_);
    return v___x_1165_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__6() -> *mut LeanObject {
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1166_ = l_Lean_Parser_Term_motive;
    v___x_1167_ = l_Lean_Parser_optional(v___x_1166_);
    return v___x_1167_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__8() -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    v___x_1169_ = l_Lean_Parser_Tactic_match___closed__7;
    v___x_1170_ = l_Lean_Parser_symbol(v___x_1169_);
    return v___x_1170_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__9() -> *mut LeanObject {
    let mut v___x_1171_: u8 = 0;
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1171_ = 0;
    v___x_1172_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__8_once),
        _init_l_Lean_Parser_Tactic_match___closed__8,
    );
    v___x_1173_ = l_Lean_Parser_Tactic_match___closed__7;
    v___x_1174_ = l_Lean_Parser_Term_matchDiscr;
    v___x_1175_ = l_Lean_Parser_sepBy1(v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
    return v___x_1175_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__11() -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ = l_Lean_Parser_Tactic_match___closed__10;
    v___x_1178_ = l_Lean_Parser_symbol(v___x_1177_);
    return v___x_1178_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__12() -> *mut LeanObject {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_Parser_Tactic_matchAlts;
    v___x_1180_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__11_once),
        _init_l_Lean_Parser_Tactic_match___closed__11,
    );
    v___x_1181_ = l_Lean_Parser_andthen(v___x_1180_, v___x_1179_);
    return v___x_1181_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__13() -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__12_once),
        _init_l_Lean_Parser_Tactic_match___closed__12,
    );
    v___x_1183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__9_once),
        _init_l_Lean_Parser_Tactic_match___closed__9,
    );
    v___x_1184_ = l_Lean_Parser_andthen(v___x_1183_, v___x_1182_);
    return v___x_1184_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__14() -> *mut LeanObject {
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1185_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__13_once),
        _init_l_Lean_Parser_Tactic_match___closed__13,
    );
    v___x_1186_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__6_once),
        _init_l_Lean_Parser_Tactic_match___closed__6,
    );
    v___x_1187_ = l_Lean_Parser_andthen(v___x_1186_, v___x_1185_);
    return v___x_1187_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__15() -> *mut LeanObject {
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    v___x_1188_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__14_once),
        _init_l_Lean_Parser_Tactic_match___closed__14,
    );
    v___x_1189_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__5_once),
        _init_l_Lean_Parser_Tactic_match___closed__5,
    );
    v___x_1190_ = l_Lean_Parser_andthen(v___x_1189_, v___x_1188_);
    return v___x_1190_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__16() -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__15_once),
        _init_l_Lean_Parser_Tactic_match___closed__15,
    );
    v___x_1192_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__4_once),
        _init_l_Lean_Parser_Tactic_match___closed__4,
    );
    v___x_1193_ = l_Lean_Parser_andthen(v___x_1192_, v___x_1191_);
    return v___x_1193_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__17() -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1194_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__16_once),
        _init_l_Lean_Parser_Tactic_match___closed__16,
    );
    v___x_1195_ = l_Lean_Parser_leadPrec;
    v___x_1196_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1197_ = l_Lean_Parser_leadingNode(v___x_1196_, v___x_1195_, v___x_1194_);
    return v___x_1197_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__18() -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    v___x_1198_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__17_once),
        _init_l_Lean_Parser_Tactic_match___closed__17,
    );
    v___x_1199_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__2_once),
        _init_l_Lean_Parser_Tactic_match___closed__2,
    );
    v___x_1200_ = l_Lean_Parser_withAntiquot(v___x_1199_, v___x_1198_);
    return v___x_1200_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match___closed__19() -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__18_once),
        _init_l_Lean_Parser_Tactic_match___closed__18,
    );
    v___x_1202_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1203_ = l_Lean_Parser_withCache(v___x_1202_, v___x_1201_);
    return v___x_1203_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match() -> *mut LeanObject {
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    v___x_1204_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match___closed__19_once),
        _init_l_Lean_Parser_Tactic_match___closed__19,
    );
    return v___x_1204_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1()
-> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    v___x_1206_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1;
    v___x_1207_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1208_ = l_Lean_Parser_Tactic_match;
    v___x_1209_ = lean_unsigned_to_nat(1000);
    v___x_1210_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1206_, v___x_1207_, v___x_1208_, v___x_1209_);
    return v___x_1210_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1___boxed(
    mut v_a_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1212_: *mut LeanObject = core::ptr::null_mut();
    v_res_1212_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
    return v_res_1212_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3()
-> *mut LeanObject {
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1215_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1216_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___closed__0;
    v___x_1217_ = l_Lean_addBuiltinDocString(v___x_1215_, v___x_1216_);
    return v___x_1217_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3___boxed(
    mut v_a_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1219_: *mut LeanObject = core::ptr::null_mut();
    v_res_1219_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
    return v_res_1219_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5()
-> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1247_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___closed__6;
    v___x_1248_ = l_Lean_addBuiltinDeclarationRanges(v___x_1246_, v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5___boxed(
    mut v_a_1249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1250_: *mut LeanObject = core::ptr::null_mut();
    v_res_1250_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
    return v_res_1250_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchRhs_formatter(
    mut v_a_1256_: *mut LeanObject,
    mut v_a_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
    mut v_a_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ = l_Lean_Parser_Tactic_matchRhs_formatter___closed__0;
    v___x_1262_ = l_Lean_Parser_Tactic_matchRhs_formatter___closed__2;
    v___x_1263_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1261_,
        v___x_1262_,
        v_a_1256_,
        v_a_1257_,
        v_a_1258_,
        v_a_1259_,
    );
    return v___x_1263_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchRhs_formatter___boxed(
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
    mut v_a_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1269_: *mut LeanObject = core::ptr::null_mut();
    v_res_1269_ =
        l_Lean_Parser_Tactic_matchRhs_formatter(v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
    lean_dec(v_a_1267_);
    lean_dec_ref(v_a_1266_);
    lean_dec(v_a_1265_);
    lean_dec_ref(v_a_1264_);
    return v_res_1269_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchAlts_formatter(
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1275_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchRhs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1276_ = l_Lean_Parser_Term_matchAlts_formatter(
        v___x_1275_,
        v_a_1270_,
        v_a_1271_,
        v_a_1272_,
        v_a_1273_,
    );
    return v___x_1276_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchAlts_formatter___boxed(
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1282_ =
        l_Lean_Parser_Tactic_matchAlts_formatter(v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
    lean_dec(v_a_1280_);
    lean_dec_ref(v_a_1279_);
    lean_dec(v_a_1278_);
    lean_dec_ref(v_a_1277_);
    return v_res_1282_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__10() -> *mut LeanObject {
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1309_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchAlts_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1310_ = lean_alloc_closure(
        l_Lean_ppDedent_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1310_, 0, v___x_1309_);
    return v___x_1310_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__11() -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__10_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__10,
    );
    v___x_1312_ = l_Lean_Parser_Tactic_match_formatter___closed__9;
    v___x_1313_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1313_, 0, v___x_1312_);
    lean_closure_set(v___x_1313_, 1, v___x_1311_);
    return v___x_1313_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__12() -> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__11_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__11,
    );
    v___x_1315_ = l_Lean_Parser_Tactic_match_formatter___closed__8;
    v___x_1316_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1316_, 0, v___x_1315_);
    lean_closure_set(v___x_1316_, 1, v___x_1314_);
    return v___x_1316_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__13() -> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__12_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__12,
    );
    v___x_1318_ = l_Lean_Parser_Tactic_match_formatter___closed__5;
    v___x_1319_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1319_, 0, v___x_1318_);
    lean_closure_set(v___x_1319_, 1, v___x_1317_);
    return v___x_1319_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__14() -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__13_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__13,
    );
    v___x_1321_ = l_Lean_Parser_Tactic_match_formatter___closed__3;
    v___x_1322_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1322_, 0, v___x_1321_);
    lean_closure_set(v___x_1322_, 1, v___x_1320_);
    return v___x_1322_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__15() -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    v___x_1323_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__14_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__14,
    );
    v___x_1324_ = l_Lean_Parser_Tactic_match_formatter___closed__1;
    v___x_1325_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1325_, 0, v___x_1324_);
    lean_closure_set(v___x_1325_, 1, v___x_1323_);
    return v___x_1325_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_formatter___closed__16() -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__15_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__15,
    );
    v___x_1327_ = l_Lean_Parser_leadPrec;
    v___x_1328_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1329_ = lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1329_, 0, v___x_1328_);
    lean_closure_set(v___x_1329_, 1, v___x_1327_);
    lean_closure_set(v___x_1329_, 2, v___x_1326_);
    return v___x_1329_;
}
pub unsafe fn l_Lean_Parser_Tactic_match_formatter(
    mut v_a_1330_: *mut LeanObject,
    mut v_a_1331_: *mut LeanObject,
    mut v_a_1332_: *mut LeanObject,
    mut v_a_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1335_ = l_Lean_Parser_Tactic_match_formatter___closed__0;
    v___x_1336_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_formatter___closed__16_once),
        _init_l_Lean_Parser_Tactic_match_formatter___closed__16,
    );
    v___x_1337_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1335_,
        v___x_1336_,
        v_a_1330_,
        v_a_1331_,
        v_a_1332_,
        v_a_1333_,
    );
    return v___x_1337_;
}
pub unsafe fn l_Lean_Parser_Tactic_match_formatter___boxed(
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
    mut v_a_1340_: *mut LeanObject,
    mut v_a_1341_: *mut LeanObject,
    mut v_a_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1343_: *mut LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_Lean_Parser_Tactic_match_formatter(v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_);
    lean_dec(v_a_1341_);
    lean_dec_ref(v_a_1340_);
    lean_dec(v_a_1339_);
    lean_dec_ref(v_a_1338_);
    return v_res_1343_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13()
-> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1352_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1353_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___closed__0;
    v___x_1354_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_match_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1351_,
        v___x_1352_,
        v___x_1353_,
        v___x_1354_,
    );
    return v___x_1355_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13___boxed(
    mut v_a_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1357_: *mut LeanObject = core::ptr::null_mut();
    v_res_1357_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
    return v_res_1357_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchRhs_parenthesizer(
    mut v_a_1363_: *mut LeanObject,
    mut v_a_1364_: *mut LeanObject,
    mut v_a_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    v___x_1368_ = l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__0;
    v___x_1369_ = l_Lean_Parser_Tactic_matchRhs_parenthesizer___closed__2;
    v___x_1370_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(
        v___x_1368_,
        v___x_1369_,
        v_a_1363_,
        v_a_1364_,
        v_a_1365_,
        v_a_1366_,
    );
    return v___x_1370_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed(
    mut v_a_1371_: *mut LeanObject,
    mut v_a_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1376_: *mut LeanObject = core::ptr::null_mut();
    v_res_1376_ =
        l_Lean_Parser_Tactic_matchRhs_parenthesizer(v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
    lean_dec(v_a_1374_);
    lean_dec_ref(v_a_1373_);
    lean_dec(v_a_1372_);
    lean_dec_ref(v_a_1371_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchAlts_parenthesizer(
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
    mut v_a_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1382_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1383_ = l_Lean_Parser_Term_matchAlts_parenthesizer(
        v___x_1382_,
        v_a_1377_,
        v_a_1378_,
        v_a_1379_,
        v_a_1380_,
    );
    return v___x_1383_;
}
pub unsafe fn l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed(
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
    mut v_a_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1389_: *mut LeanObject = core::ptr::null_mut();
    v_res_1389_ =
        l_Lean_Parser_Tactic_matchAlts_parenthesizer(v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
    lean_dec(v_a_1387_);
    lean_dec_ref(v_a_1386_);
    lean_dec(v_a_1385_);
    lean_dec_ref(v_a_1384_);
    return v_res_1389_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10() -> *mut LeanObject {
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1416_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1417_ = lean_alloc_closure(
        l_Lean_Parser_ppDedent_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1417_, 0, v___x_1416_);
    return v___x_1417_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11() -> *mut LeanObject {
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__10_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__10,
    );
    v___x_1419_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__9;
    v___x_1420_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1420_, 0, v___x_1419_);
    lean_closure_set(v___x_1420_, 1, v___x_1418_);
    return v___x_1420_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12() -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__11_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__11,
    );
    v___x_1422_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__8;
    v___x_1423_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1423_, 0, v___x_1422_);
    lean_closure_set(v___x_1423_, 1, v___x_1421_);
    return v___x_1423_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13() -> *mut LeanObject {
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__12_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__12,
    );
    v___x_1425_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__5;
    v___x_1426_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1426_, 0, v___x_1425_);
    lean_closure_set(v___x_1426_, 1, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14() -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__13_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__13,
    );
    v___x_1428_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__3;
    v___x_1429_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1429_, 0, v___x_1428_);
    lean_closure_set(v___x_1429_, 1, v___x_1427_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15() -> *mut LeanObject {
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__14_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__14,
    );
    v___x_1431_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__1;
    v___x_1432_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1432_, 0, v___x_1431_);
    lean_closure_set(v___x_1432_, 1, v___x_1430_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16() -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__15_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__15,
    );
    v___x_1434_ = l_Lean_Parser_leadPrec;
    v___x_1435_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1436_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1436_, 0, v___x_1435_);
    lean_closure_set(v___x_1436_, 1, v___x_1434_);
    lean_closure_set(v___x_1436_, 2, v___x_1433_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Parser_Tactic_match_parenthesizer(
    mut v_a_1437_: *mut LeanObject,
    mut v_a_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Lean_Parser_Tactic_match_parenthesizer___closed__0;
    v___x_1443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_match_parenthesizer___closed__16_once),
        _init_l_Lean_Parser_Tactic_match_parenthesizer___closed__16,
    );
    v___x_1444_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1442_,
        v___x_1443_,
        v_a_1437_,
        v_a_1438_,
        v_a_1439_,
        v_a_1440_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Parser_Tactic_match_parenthesizer___boxed(
    mut v_a_1445_: *mut LeanObject,
    mut v_a_1446_: *mut LeanObject,
    mut v_a_1447_: *mut LeanObject,
    mut v_a_1448_: *mut LeanObject,
    mut v_a_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1450_: *mut LeanObject = core::ptr::null_mut();
    v_res_1450_ =
        l_Lean_Parser_Tactic_match_parenthesizer(v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
    lean_dec(v_a_1448_);
    lean_dec_ref(v_a_1447_);
    lean_dec(v_a_1446_);
    lean_dec_ref(v_a_1445_);
    return v_res_1450_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21()
-> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1459_ = l_Lean_Parser_Tactic_match___closed__1;
    v___x_1460_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___closed__0;
    v___x_1461_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_match_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1462_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1458_,
        v___x_1459_,
        v___x_1460_,
        v___x_1461_,
    );
    return v___x_1462_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21___boxed(
    mut v_a_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1464_: *mut LeanObject = core::ptr::null_mut();
    v_res_1464_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
    return v_res_1464_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__2() -> *mut LeanObject {
    let mut v___x_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_1471_ = 0;
    v___x_1472_ = 1;
    v___x_1473_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1474_ = l_Lean_Parser_Tactic_introMatch___closed__0;
    v___x_1475_ = l_Lean_Parser_mkAntiquot(v___x_1474_, v___x_1473_, v___x_1472_, v___x_1471_);
    return v___x_1475_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__4() -> *mut LeanObject {
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    v___x_1477_ = 0;
    v___x_1478_ = l_Lean_Parser_Tactic_introMatch___closed__3;
    v___x_1479_ = l_Lean_Parser_nonReservedSymbol(v___x_1478_, v___x_1477_);
    return v___x_1479_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__5() -> *mut LeanObject {
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    v___x_1480_ = l_Lean_Parser_Tactic_matchAlts;
    v___x_1481_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__4_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__4,
    );
    v___x_1482_ = l_Lean_Parser_andthen(v___x_1481_, v___x_1480_);
    return v___x_1482_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__6() -> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__5_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__5,
    );
    v___x_1484_ = lean_unsigned_to_nat(1024);
    v___x_1485_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1486_ = l_Lean_Parser_leadingNode(v___x_1485_, v___x_1484_, v___x_1483_);
    return v___x_1486_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__7() -> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    v___x_1487_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__6_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__6,
    );
    v___x_1488_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__2_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__2,
    );
    v___x_1489_ = l_Lean_Parser_withAntiquot(v___x_1488_, v___x_1487_);
    return v___x_1489_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch___closed__8() -> *mut LeanObject {
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__7_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__7,
    );
    v___x_1491_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1492_ = l_Lean_Parser_withCache(v___x_1491_, v___x_1490_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch() -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch___closed__8_once),
        _init_l_Lean_Parser_Tactic_introMatch___closed__8,
    );
    return v___x_1493_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1()
-> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1___closed__1;
    v___x_1496_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1497_ = l_Lean_Parser_Tactic_introMatch;
    v___x_1498_ = lean_unsigned_to_nat(1000);
    v___x_1499_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1495_, v___x_1496_, v___x_1497_, v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1___boxed(
    mut v_a_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
    return v_res_1501_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3()
-> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1529_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___closed__6;
    v___x_1530_ = l_Lean_addBuiltinDeclarationRanges(v___x_1528_, v___x_1529_);
    return v___x_1530_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3___boxed(
    mut v_a_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1532_: *mut LeanObject = core::ptr::null_mut();
    v_res_1532_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
    return v_res_1532_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1544_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchAlts_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1545_ = l_Lean_Parser_Tactic_introMatch_formatter___closed__1;
    v___x_1546_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1546_, 0, v___x_1545_);
    lean_closure_set(v___x_1546_, 1, v___x_1544_);
    return v___x_1546_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_formatter___closed__2_once),
        _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__2,
    );
    v___x_1548_ = lean_unsigned_to_nat(1024);
    v___x_1549_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1550_ = lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1550_, 0, v___x_1549_);
    lean_closure_set(v___x_1550_, 1, v___x_1548_);
    lean_closure_set(v___x_1550_, 2, v___x_1547_);
    return v___x_1550_;
}
pub unsafe fn l_Lean_Parser_Tactic_introMatch_formatter(
    mut v_a_1551_: *mut LeanObject,
    mut v_a_1552_: *mut LeanObject,
    mut v_a_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Lean_Parser_Tactic_introMatch_formatter___closed__0;
    v___x_1557_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_formatter___closed__3_once),
        _init_l_Lean_Parser_Tactic_introMatch_formatter___closed__3,
    );
    v___x_1558_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1556_,
        v___x_1557_,
        v_a_1551_,
        v_a_1552_,
        v_a_1553_,
        v_a_1554_,
    );
    return v___x_1558_;
}
pub unsafe fn l_Lean_Parser_Tactic_introMatch_formatter___boxed(
    mut v_a_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_a_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1564_: *mut LeanObject = core::ptr::null_mut();
    v_res_1564_ =
        l_Lean_Parser_Tactic_introMatch_formatter(v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
    lean_dec(v_a_1562_);
    lean_dec_ref(v_a_1561_);
    lean_dec(v_a_1560_);
    lean_dec_ref(v_a_1559_);
    return v_res_1564_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7()
-> *mut LeanObject {
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1573_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1574_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___closed__0;
    v___x_1575_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_introMatch_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1576_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1572_,
        v___x_1573_,
        v___x_1574_,
        v___x_1575_,
    );
    return v___x_1576_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7___boxed(
    mut v_a_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
    return v_res_1578_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1590_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchAlts_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1591_ = l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__1;
    v___x_1592_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1592_, 0, v___x_1591_);
    lean_closure_set(v___x_1592_, 1, v___x_1590_);
    return v___x_1592_;
}
pub unsafe fn _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__2,
    );
    v___x_1594_ = lean_unsigned_to_nat(1024);
    v___x_1595_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1596_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1596_, 0, v___x_1595_);
    lean_closure_set(v___x_1596_, 1, v___x_1594_);
    lean_closure_set(v___x_1596_, 2, v___x_1593_);
    return v___x_1596_;
}
pub unsafe fn l_Lean_Parser_Tactic_introMatch_parenthesizer(
    mut v_a_1597_: *mut LeanObject,
    mut v_a_1598_: *mut LeanObject,
    mut v_a_1599_: *mut LeanObject,
    mut v_a_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__0;
    v___x_1603_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Tactic_introMatch_parenthesizer___closed__3,
    );
    v___x_1604_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1602_,
        v___x_1603_,
        v_a_1597_,
        v_a_1598_,
        v_a_1599_,
        v_a_1600_,
    );
    return v___x_1604_;
}
pub unsafe fn l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed(
    mut v_a_1605_: *mut LeanObject,
    mut v_a_1606_: *mut LeanObject,
    mut v_a_1607_: *mut LeanObject,
    mut v_a_1608_: *mut LeanObject,
    mut v_a_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1610_: *mut LeanObject = core::ptr::null_mut();
    v_res_1610_ =
        l_Lean_Parser_Tactic_introMatch_parenthesizer(v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
    lean_dec(v_a_1608_);
    lean_dec_ref(v_a_1607_);
    lean_dec(v_a_1606_);
    lean_dec_ref(v_a_1605_);
    return v_res_1610_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1619_ = l_Lean_Parser_Tactic_introMatch___closed__1;
    v___x_1620_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___closed__0;
    v___x_1621_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_introMatch_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1622_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1618_,
        v___x_1619_,
        v___x_1620_,
        v___x_1621_,
    );
    return v___x_1622_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11___boxed(
    mut v_a_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1624_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
    return v_res_1624_;
}
pub unsafe fn _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ = l_Lean_Parser_Tactic_matchRhs;
    v___x_1635_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1635_, 0, v___x_1634_);
    return v___x_1635_;
}
pub unsafe fn _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchRhs_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1639_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1639_, 0, v___x_1638_);
    return v___x_1639_;
}
pub unsafe fn _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = lean_alloc_closure(
        l_Lean_Parser_Tactic_matchRhs_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1641_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1641_, 0, v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__1_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
    v___x_1644_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__3_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
    v___x_1645_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__4_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
    v___x_1646_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__5_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_;
    v___x_1647_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__9_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_;
    v___x_1648_ = l_Lean_Parser_registerAlias(
        v___x_1643_,
        v___x_1644_,
        v___x_1645_,
        v___x_1646_,
        v___x_1647_,
    );
    if lean_obj_tag(v___x_1648_) == 0 {
        let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_1648_, 1);
        v___x_1649_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__6_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
        v___x_1650_ = l_Lean_PrettyPrinter_Formatter_registerAlias(v___x_1643_, v___x_1649_);
        if lean_obj_tag(v___x_1650_) == 0 {
            let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1650_, 1);
            v___x_1651_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn___closed__7_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_);
            v___x_1652_ =
                l_Lean_PrettyPrinter_Parenthesizer_registerAlias(v___x_1643_, v___x_1651_);
            return v___x_1652_;
        } else {
            return v___x_1650_;
        }
    } else {
        return v___x_1648_;
    }
}
pub unsafe fn l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2____boxed(
    mut v_a_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1654_: *mut LeanObject = core::ptr::null_mut();
    v_res_1654_ = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
    return v_res_1654_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_255552617____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Tactic_unknown = _init_l_Lean_Parser_Tactic_unknown();
    lean_mark_persistent(l_Lean_Parser_Tactic_unknown);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_unknown___regBuiltin_Lean_Parser_Tactic_unknown_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Tactic_nestedTactic = _init_l_Lean_Parser_Tactic_nestedTactic();
    lean_mark_persistent(l_Lean_Parser_Tactic_nestedTactic);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_nestedTactic___regBuiltin_Lean_Parser_Tactic_nestedTactic_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Tactic_matchRhs = _init_l_Lean_Parser_Tactic_matchRhs();
    lean_mark_persistent(l_Lean_Parser_Tactic_matchRhs);
    l_Lean_Parser_Tactic_matchAlts = _init_l_Lean_Parser_Tactic_matchAlts();
    lean_mark_persistent(l_Lean_Parser_Tactic_matchAlts);
    l_Lean_Parser_Tactic_match = _init_l_Lean_Parser_Tactic_match();
    lean_mark_persistent(l_Lean_Parser_Tactic_match);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_formatter__13();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_match___regBuiltin_Lean_Parser_Tactic_match_parenthesizer__21();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Tactic_introMatch = _init_l_Lean_Parser_Tactic_introMatch();
    lean_mark_persistent(l_Lean_Parser_Tactic_introMatch);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_introMatch___regBuiltin_Lean_Parser_Tactic_introMatch_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Tactic_0__Lean_Parser_Tactic_initFn_00___x40_Lean_Parser_Tactic_2276592124____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Term(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Parser_Tactic_Doc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser_Tactic(builtin);
}
