// Lean compiler output
// Module: Lean.Parser.Level
// Imports: Lean.Parser.Extra
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_categoryParser, l_Lean_Parser_checkPrec,
    l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot, l_Lean_Parser_nonReservedSymbol,
    l_Lean_Parser_skip, l_Lean_Parser_symbol, l_Lean_Parser_trailingNode,
    l_Lean_Parser_withAntiquot, l_Lean_Parser_withoutPosition,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_addBuiltinLeadingParser, l_Lean_Parser_addBuiltinTrailingParser,
    l_Lean_Parser_registerBuiltinParserAttribute,
};
use crate::r#gen::Lean::Parser::Extra::{
    initialize_Lean_Parser_Extra, l_Lean_Parser_ident, l_Lean_Parser_ident_formatter___boxed,
    l_Lean_Parser_ident_parenthesizer___boxed, l_Lean_Parser_leadingNode_formatter___boxed,
    l_Lean_Parser_many1, l_Lean_Parser_many1_formatter___boxed,
    l_Lean_Parser_many1_parenthesizer___boxed, l_Lean_Parser_mkAntiquot_formatter___boxed,
    l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_nonReservedSymbol_formatter___boxed,
    l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, l_Lean_Parser_numLit,
    l_Lean_Parser_numLit_formatter___boxed, l_Lean_Parser_numLit_parenthesizer___boxed,
    l_Lean_Parser_ppSpace_parenthesizer___boxed, l_Lean_Parser_symbol_formatter___boxed,
    l_Lean_Parser_symbol_parenthesizer___boxed, l_Lean_Parser_withoutPosition_formatter___boxed,
    l_Lean_Parser_withoutPosition_parenthesizer___boxed, runtime_initialize_Lean_Parser_Extra,
};
use crate::r#gen::Lean::Parser::Types::{l_Lean_Parser_maxPrec, l_Lean_Parser_withCache};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter,
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_categoryParser_formatter,
    l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_pushLine___redArg,
    l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg,
    l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent,
    lean_obj_once, lean_unsigned_to_nat,
};
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 108, 101, 118, 101, 108, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,9745384030107003485 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 97, 116, 101, 103, 111, 114, 121, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 118, 101, 108, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11615938313939332388 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,5590899989335360147 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,6386160366488538211 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [76, 101, 118, 101, 108, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,14494391219297291524 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,7785265914445005157 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,14939046515727124016 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,1933950152129716673 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,5398980242634698616 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,479258365174138313 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,15099957416863655180 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,15684945113032081877 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,3094884611430224490 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_levelParser___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,18250387975948097528 as *mut LeanObject] };
static mut l_Lean_Parser_levelParser___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_levelParser___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren___closed__0_value: LeanStringObject<6> = LeanStringObject {
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
static mut l_Lean_Parser_Level_paren___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Level_paren___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Level_paren___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Level_paren___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l_Lean_Parser_Level_paren___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject,
        16533827001853265987 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Level_paren___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_paren___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Level_paren___closed__3_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Parser_Level_paren___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_paren___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Level_paren___closed__7_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_Parser_Level_paren___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__7_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_paren___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_paren___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_paren___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_paren: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__1_value) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__4_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_levelParser_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_withoutPosition_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__4_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__6_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_formatter___closed__7_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_formatter___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject,16533827001853265987 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject,250347350324661718 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_levelParser_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_withoutPosition_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__4_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__6_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_paren_parenthesizer___closed__7_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_paren_parenthesizer___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_paren_parenthesizer___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_paren___closed__0_value) as *mut LeanObject,16533827001853265987 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject,15935465693922714490 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max___closed__0_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [109, 97, 120, 0],
};
static mut l_Lean_Parser_Level_max___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Level_max___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Level_max___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Level_max___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l_Lean_Parser_Level_max___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,
        7017890982578468202 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Level_max___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_max___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_max: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 23 as usize) << 1) | 1) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__1_value) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 22 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__4_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_formatter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Level_max_formatter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Level_max_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_formatter___closed__1_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_max_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_max_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_formatter___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_max_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_formatter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_formatter___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_formatter___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_formatter___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_formatter___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_formatter___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_formatter___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_formatter___closed__7: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,7017890982578468202 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject,9630319634850242851 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_max_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_parenthesizer___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_max_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_parenthesizer___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_max_parenthesizer___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_ppSpace_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Level_max_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_max_parenthesizer___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_max_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_parenthesizer___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_parenthesizer___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Level_max_parenthesizer___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_max_parenthesizer___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_max___closed__0_value) as *mut LeanObject,7017890982578468202 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject,9731699799936889687 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_imax___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 109, 97, 120, 0],
};
static mut l_Lean_Parser_Level_imax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Level_imax___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Level_imax___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Level_imax___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l_Lean_Parser_Level_imax___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,
        2051294913818044796 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Level_imax___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_imax___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_imax: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__1_value) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__4_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_imax_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_imax_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_imax_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_imax_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax_formatter___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_imax_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax_formatter___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,2051294913818044796 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject,16783204708083767893 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_imax_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_imax_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_imax_parenthesizer___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_imax_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_imax___closed__0_value) as *mut LeanObject,2051294913818044796 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject,4738646117334012209 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_hole___closed__0_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Parser_Level_hole___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Level_hole___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Level_hole___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Level_hole___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l_Lean_Parser_Level_hole___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject,
        1315703591728338576 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Level_hole___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_hole___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_hole___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Level_hole___closed__3_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l_Lean_Parser_Level_hole___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_hole___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_hole___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_hole___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_hole___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_hole___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_hole___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_hole___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_hole___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_hole: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut LeanObject,((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__1_value) as *mut LeanObject,((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 26 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__4_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_formatter___closed__2_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_hole_formatter___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_formatter___closed__2_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject,1315703591728338576 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject,16263654809068730673 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_hole_parenthesizer___closed__2_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_hole_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_hole_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_hole_parenthesizer___closed__2_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_hole___closed__0_value) as *mut LeanObject,1315703591728338576 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject,10003456462949990997 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_num___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_num___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_num___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_num___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_num: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 117, 109, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__0_value) as *mut LeanObject,16755121585154003148 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 29 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__1_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__4_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_num_formatter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_numLit_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Level_num_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_num_formatter___closed__0_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_num_parenthesizer___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_num_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Level_num_parenthesizer___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_numLit_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Level_num_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_num_parenthesizer___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_ident___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_ident___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_ident: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__0_value) as *mut LeanObject,9445620412047803547 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__1_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__4_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_ident_formatter___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Level_ident_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_ident_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_ident_parenthesizer___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Level_ident_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_ident_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [97, 100, 100, 76, 105, 116, 0],
};
static mut l_Lean_Parser_Level_addLit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Level_addLit___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Level_addLit___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Level_addLit___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
pub static l_Lean_Parser_Level_addLit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__0_value) as *mut LeanObject,
        12560806670959244085 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Level_addLit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 43, 32, 0],
};
static mut l_Lean_Parser_Level_addLit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__2_value) as *mut LeanObject;
static mut l_Lean_Parser_Level_addLit___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_addLit___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_addLit___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_addLit___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Level_addLit___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Level_addLit___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Level_addLit: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 33 as usize) << 1) | 1) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__0_value) as *mut LeanObject,((( 24 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__1_value) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 32 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__3_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit_formatter___closed__0_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_addLit_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_addLit_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_num_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_addLit_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit_formatter___closed__1_value) as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__0_value) as *mut LeanObject,12560806670959244085 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__0_value) as *mut LeanObject,3767795761449765416 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_addLit_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Level_addLit_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Level_addLit_parenthesizer___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Level_num_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Level_addLit_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Level_addLit_parenthesizer___closed__1_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__value) as *mut LeanObject,11423656342444823216 as *mut LeanObject] };
static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Level_addLit___closed__0_value) as *mut LeanObject,12560806670959244085 as *mut LeanObject] };
pub static l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__0_value) as *mut LeanObject,18075488229941091892 as *mut LeanObject] };
static mut l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    v___x_1158_ = lean_unsigned_to_nat(2271617841);
    v___x_1159_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
    v___x_1160_ = l_Lean_Name_num___override(v___x_1159_, v___x_1158_);
    return v___x_1160_;
}
pub unsafe fn _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___x_1162_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
    v___x_1163_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
    v___x_1164_ = l_Lean_Name_str___override(v___x_1163_, v___x_1162_);
    return v___x_1164_;
}
pub unsafe fn _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    v___x_1166_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
    v___x_1167_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
    v___x_1168_ = l_Lean_Name_str___override(v___x_1167_, v___x_1166_);
    return v___x_1168_;
}
pub unsafe fn _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    v___x_1169_ = lean_unsigned_to_nat(2);
    v___x_1170_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
    v___x_1171_ = l_Lean_Name_num___override(v___x_1170_, v___x_1169_);
    return v___x_1171_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    v___x_1173_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
    v___x_1174_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_;
    v___x_1175_ = 0;
    v___x_1176_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2__once), _init_l___private_Lean_Parser_Level_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_);
    v___x_1177_ = l_Lean_Parser_registerBuiltinParserAttribute(
        v___x_1173_,
        v___x_1174_,
        v___x_1175_,
        v___x_1176_,
    );
    return v___x_1177_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2____boxed(
    mut v_a_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
    return v_res_1179_;
}
pub unsafe fn l_Lean_Parser_levelParser(mut v_rbp_1182_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___x_1183_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1184_ = l_Lean_Parser_categoryParser(v___x_1183_, v_rbp_1182_);
    return v___x_1184_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__2() -> *mut LeanObject {
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: u8 = 0;
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    v___x_1191_ = 0;
    v___x_1192_ = 1;
    v___x_1193_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1194_ = l_Lean_Parser_Level_paren___closed__0;
    v___x_1195_ = l_Lean_Parser_mkAntiquot(v___x_1194_, v___x_1193_, v___x_1192_, v___x_1191_);
    return v___x_1195_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__4() -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Lean_Parser_Level_paren___closed__3;
    v___x_1198_ = l_Lean_Parser_symbol(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__5() -> *mut LeanObject {
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1199_ = lean_unsigned_to_nat(0);
    v___x_1200_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1201_ = l_Lean_Parser_categoryParser(v___x_1200_, v___x_1199_);
    return v___x_1201_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__6() -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    v___x_1202_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__5_once),
        _init_l_Lean_Parser_Level_paren___closed__5,
    );
    v___x_1203_ = l_Lean_Parser_withoutPosition(v___x_1202_);
    return v___x_1203_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__8() -> *mut LeanObject {
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Lean_Parser_Level_paren___closed__7;
    v___x_1206_ = l_Lean_Parser_symbol(v___x_1205_);
    return v___x_1206_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__9() -> *mut LeanObject {
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    v___x_1207_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__8_once),
        _init_l_Lean_Parser_Level_paren___closed__8,
    );
    v___x_1208_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__6_once),
        _init_l_Lean_Parser_Level_paren___closed__6,
    );
    v___x_1209_ = l_Lean_Parser_andthen(v___x_1208_, v___x_1207_);
    return v___x_1209_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__10() -> *mut LeanObject {
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    v___x_1210_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__9_once),
        _init_l_Lean_Parser_Level_paren___closed__9,
    );
    v___x_1211_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__4_once),
        _init_l_Lean_Parser_Level_paren___closed__4,
    );
    v___x_1212_ = l_Lean_Parser_andthen(v___x_1211_, v___x_1210_);
    return v___x_1212_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__11() -> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__10_once),
        _init_l_Lean_Parser_Level_paren___closed__10,
    );
    v___x_1214_ = lean_unsigned_to_nat(1024);
    v___x_1215_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1216_ = l_Lean_Parser_leadingNode(v___x_1215_, v___x_1214_, v___x_1213_);
    return v___x_1216_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__12() -> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__11_once),
        _init_l_Lean_Parser_Level_paren___closed__11,
    );
    v___x_1218_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__2_once),
        _init_l_Lean_Parser_Level_paren___closed__2,
    );
    v___x_1219_ = l_Lean_Parser_withAntiquot(v___x_1218_, v___x_1217_);
    return v___x_1219_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren___closed__13() -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__12_once),
        _init_l_Lean_Parser_Level_paren___closed__12,
    );
    v___x_1221_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1222_ = l_Lean_Parser_withCache(v___x_1221_, v___x_1220_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_Parser_Level_paren() -> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    v___x_1223_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_paren___closed__13_once),
        _init_l_Lean_Parser_Level_paren___closed__13,
    );
    return v___x_1223_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1()
-> *mut LeanObject {
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_1225_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1226_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1227_ = l_Lean_Parser_Level_paren;
    v___x_1228_ = lean_unsigned_to_nat(1000);
    v___x_1229_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1225_, v___x_1226_, v___x_1227_, v___x_1228_);
    return v___x_1229_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1___boxed(
    mut v_a_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1231_: *mut LeanObject = core::ptr::null_mut();
    v_res_1231_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
    return v_res_1231_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3()
-> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1259_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___closed__6;
    v___x_1260_ = l_Lean_addBuiltinDeclarationRanges(v___x_1258_, v___x_1259_);
    return v___x_1260_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3___boxed(
    mut v_a_1261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1262_: *mut LeanObject = core::ptr::null_mut();
    v_res_1262_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
    return v_res_1262_;
}
pub unsafe fn l_Lean_Parser_levelParser_formatter___redArg(
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    v___x_1268_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1269_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(
        v___x_1268_,
        v_a_1263_,
        v_a_1264_,
        v_a_1265_,
        v_a_1266_,
    );
    return v___x_1269_;
}
pub unsafe fn l_Lean_Parser_levelParser_formatter___redArg___boxed(
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
    mut v_a_1272_: *mut LeanObject,
    mut v_a_1273_: *mut LeanObject,
    mut v_a_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1275_: *mut LeanObject = core::ptr::null_mut();
    v_res_1275_ =
        l_Lean_Parser_levelParser_formatter___redArg(v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
    lean_dec(v_a_1273_);
    lean_dec_ref(v_a_1272_);
    lean_dec(v_a_1271_);
    lean_dec_ref(v_a_1270_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_Parser_levelParser_formatter(
    mut v_rbp_1276_: *mut LeanObject,
    mut v_a_1277_: *mut LeanObject,
    mut v_a_1278_: *mut LeanObject,
    mut v_a_1279_: *mut LeanObject,
    mut v_a_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ =
        l_Lean_Parser_levelParser_formatter___redArg(v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_Parser_levelParser_formatter___boxed(
    mut v_rbp_1283_: *mut LeanObject,
    mut v_a_1284_: *mut LeanObject,
    mut v_a_1285_: *mut LeanObject,
    mut v_a_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_a_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Lean_Parser_levelParser_formatter(
        v_rbp_1283_,
        v_a_1284_,
        v_a_1285_,
        v_a_1286_,
        v_a_1287_,
    );
    lean_dec(v_a_1287_);
    lean_dec_ref(v_a_1286_);
    lean_dec(v_a_1285_);
    lean_dec_ref(v_a_1284_);
    lean_dec(v_rbp_1283_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Parser_Level_paren_formatter(
    mut v_a_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
    mut v_a_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_Parser_Level_paren_formatter___closed__0;
    v___x_1321_ = l_Lean_Parser_Level_paren_formatter___closed__7;
    v___x_1322_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1320_,
        v___x_1321_,
        v_a_1315_,
        v_a_1316_,
        v_a_1317_,
        v_a_1318_,
    );
    return v___x_1322_;
}
pub unsafe fn l_Lean_Parser_Level_paren_formatter___boxed(
    mut v_a_1323_: *mut LeanObject,
    mut v_a_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lean_Parser_Level_paren_formatter(v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
    lean_dec(v_a_1326_);
    lean_dec_ref(v_a_1325_);
    lean_dec(v_a_1324_);
    lean_dec_ref(v_a_1323_);
    return v_res_1328_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9()
-> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1338_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1339_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___closed__1;
    v___x_1340_ = lean_alloc_closure(
        l_Lean_Parser_Level_paren_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1341_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1337_,
        v___x_1338_,
        v___x_1339_,
        v___x_1340_,
    );
    return v___x_1341_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9___boxed(
    mut v_a_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1343_: *mut LeanObject = core::ptr::null_mut();
    v_res_1343_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
    return v_res_1343_;
}
pub unsafe fn l_Lean_Parser_levelParser_parenthesizer(
    mut v_rbp_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1351_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(
        v___x_1350_,
        v_rbp_1344_,
        v_a_1345_,
        v_a_1346_,
        v_a_1347_,
        v_a_1348_,
    );
    return v___x_1351_;
}
pub unsafe fn l_Lean_Parser_levelParser_parenthesizer___boxed(
    mut v_rbp_1352_: *mut LeanObject,
    mut v_a_1353_: *mut LeanObject,
    mut v_a_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1358_: *mut LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lean_Parser_levelParser_parenthesizer(
        v_rbp_1352_,
        v_a_1353_,
        v_a_1354_,
        v_a_1355_,
        v_a_1356_,
    );
    lean_dec(v_a_1356_);
    lean_dec_ref(v_a_1355_);
    lean_dec(v_a_1354_);
    lean_dec_ref(v_a_1353_);
    return v_res_1358_;
}
pub unsafe fn l_Lean_Parser_Level_paren_parenthesizer(
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Lean_Parser_Level_paren_parenthesizer___closed__0;
    v___x_1390_ = l_Lean_Parser_Level_paren_parenthesizer___closed__7;
    v___x_1391_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1389_,
        v___x_1390_,
        v_a_1384_,
        v_a_1385_,
        v_a_1386_,
        v_a_1387_,
    );
    return v___x_1391_;
}
pub unsafe fn l_Lean_Parser_Level_paren_parenthesizer___boxed(
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
    mut v_a_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_a_1396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1397_: *mut LeanObject = core::ptr::null_mut();
    v_res_1397_ =
        l_Lean_Parser_Level_paren_parenthesizer(v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
    lean_dec(v_a_1395_);
    lean_dec_ref(v_a_1394_);
    lean_dec(v_a_1393_);
    lean_dec_ref(v_a_1392_);
    return v_res_1397_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15()
-> *mut LeanObject {
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    v___x_1406_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1407_ = l_Lean_Parser_Level_paren___closed__1;
    v___x_1408_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___closed__1;
    v___x_1409_ = lean_alloc_closure(
        l_Lean_Parser_Level_paren_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1410_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1406_,
        v___x_1407_,
        v___x_1408_,
        v___x_1409_,
    );
    return v___x_1410_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15___boxed(
    mut v_a_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1412_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
    return v_res_1412_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__2() -> *mut LeanObject {
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = 0;
    v___x_1420_ = 1;
    v___x_1421_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1422_ = l_Lean_Parser_Level_max___closed__0;
    v___x_1423_ = l_Lean_Parser_mkAntiquot(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_);
    return v___x_1423_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__3() -> *mut LeanObject {
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = 1;
    v___x_1425_ = l_Lean_Parser_Level_max___closed__0;
    v___x_1426_ = l_Lean_Parser_nonReservedSymbol(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__4() -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = l_Lean_Parser_maxPrec;
    v___x_1428_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1429_ = l_Lean_Parser_categoryParser(v___x_1428_, v___x_1427_);
    return v___x_1429_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__5() -> *mut LeanObject {
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__4_once),
        _init_l_Lean_Parser_Level_max___closed__4,
    );
    v___x_1431_ = l_Lean_Parser_skip;
    v___x_1432_ = l_Lean_Parser_andthen(v___x_1431_, v___x_1430_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__6() -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__5_once),
        _init_l_Lean_Parser_Level_max___closed__5,
    );
    v___x_1434_ = l_Lean_Parser_many1(v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__7() -> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__6_once),
        _init_l_Lean_Parser_Level_max___closed__6,
    );
    v___x_1436_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__3_once),
        _init_l_Lean_Parser_Level_max___closed__3,
    );
    v___x_1437_ = l_Lean_Parser_andthen(v___x_1436_, v___x_1435_);
    return v___x_1437_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__8() -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__7_once),
        _init_l_Lean_Parser_Level_max___closed__7,
    );
    v___x_1439_ = lean_unsigned_to_nat(1024);
    v___x_1440_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1441_ = l_Lean_Parser_leadingNode(v___x_1440_, v___x_1439_, v___x_1438_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__9() -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__8_once),
        _init_l_Lean_Parser_Level_max___closed__8,
    );
    v___x_1443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__2_once),
        _init_l_Lean_Parser_Level_max___closed__2,
    );
    v___x_1444_ = l_Lean_Parser_withAntiquot(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max___closed__10() -> *mut LeanObject {
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___x_1445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__9_once),
        _init_l_Lean_Parser_Level_max___closed__9,
    );
    v___x_1446_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1447_ = l_Lean_Parser_withCache(v___x_1446_, v___x_1445_);
    return v___x_1447_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max() -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__10_once),
        _init_l_Lean_Parser_Level_max___closed__10,
    );
    return v___x_1448_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1()
-> *mut LeanObject {
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1450_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1451_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1452_ = l_Lean_Parser_Level_max;
    v___x_1453_ = lean_unsigned_to_nat(1000);
    v___x_1454_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1450_, v___x_1451_, v___x_1452_, v___x_1453_);
    return v___x_1454_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1___boxed(
    mut v_a_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
    return v_res_1456_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3()
-> *mut LeanObject {
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    v___x_1483_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1484_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___closed__6;
    v___x_1485_ = l_Lean_addBuiltinDeclarationRanges(v___x_1483_, v___x_1484_);
    return v___x_1485_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3___boxed(
    mut v_a_1486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1487_: *mut LeanObject = core::ptr::null_mut();
    v_res_1487_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
    return v_res_1487_;
}
pub unsafe fn l_Lean_Parser_Level_max_formatter___lam__0(
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
    mut v___y_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_1489_);
    return v___x_1493_;
}
pub unsafe fn l_Lean_Parser_Level_max_formatter___lam__0___boxed(
    mut v___y_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1499_: *mut LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Lean_Parser_Level_max_formatter___lam__0(
        v___y_1494_,
        v___y_1495_,
        v___y_1496_,
        v___y_1497_,
    );
    lean_dec(v___y_1497_);
    lean_dec_ref(v___y_1496_);
    lean_dec(v___y_1495_);
    lean_dec_ref(v___y_1494_);
    return v_res_1499_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1512_ = l_Lean_Parser_maxPrec;
    v___x_1513_ = lean_alloc_closure(
        l_Lean_Parser_levelParser_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1513_, 0, v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_formatter___closed__4() -> *mut LeanObject {
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__3_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__3,
    );
    v___f_1515_ = l_Lean_Parser_Level_max_formatter___closed__0;
    v___x_1516_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1516_, 0, v___f_1515_);
    lean_closure_set(v___x_1516_, 1, v___x_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_formatter___closed__5() -> *mut LeanObject {
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    v___x_1517_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__4_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__4,
    );
    v___x_1518_ = lean_alloc_closure(
        l_Lean_Parser_many1_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1518_, 0, v___x_1517_);
    return v___x_1518_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_formatter___closed__6() -> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__5_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__5,
    );
    v___x_1520_ = l_Lean_Parser_Level_max_formatter___closed__2;
    v___x_1521_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1521_, 0, v___x_1520_);
    lean_closure_set(v___x_1521_, 1, v___x_1519_);
    return v___x_1521_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_formatter___closed__7() -> *mut LeanObject {
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1522_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__6_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__6,
    );
    v___x_1523_ = lean_unsigned_to_nat(1024);
    v___x_1524_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1525_ = lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1525_, 0, v___x_1524_);
    lean_closure_set(v___x_1525_, 1, v___x_1523_);
    lean_closure_set(v___x_1525_, 2, v___x_1522_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_Parser_Level_max_formatter(
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Lean_Parser_Level_max_formatter___closed__1;
    v___x_1532_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__7_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__7,
    );
    v___x_1533_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1531_,
        v___x_1532_,
        v_a_1526_,
        v_a_1527_,
        v_a_1528_,
        v_a_1529_,
    );
    return v___x_1533_;
}
pub unsafe fn l_Lean_Parser_Level_max_formatter___boxed(
    mut v_a_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
    mut v_a_1538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1539_: *mut LeanObject = core::ptr::null_mut();
    v_res_1539_ = l_Lean_Parser_Level_max_formatter(v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
    lean_dec(v_a_1537_);
    lean_dec_ref(v_a_1536_);
    lean_dec(v_a_1535_);
    lean_dec_ref(v_a_1534_);
    return v_res_1539_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7()
-> *mut LeanObject {
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1548_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1549_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___closed__0;
    v___x_1550_ = lean_alloc_closure(
        l_Lean_Parser_Level_max_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1551_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1547_,
        v___x_1548_,
        v___x_1549_,
        v___x_1550_,
    );
    return v___x_1551_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7___boxed(
    mut v_a_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1553_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
    return v_res_1553_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Lean_Parser_maxPrec;
    v___x_1567_ = lean_alloc_closure(
        l_Lean_Parser_levelParser_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1567_, 0, v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__3,
    );
    v___x_1569_ = l_Lean_Parser_Level_max_parenthesizer___closed__2;
    v___x_1570_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1570_, 0, v___x_1569_);
    lean_closure_set(v___x_1570_, 1, v___x_1568_);
    return v___x_1570_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_parenthesizer___closed__5() -> *mut LeanObject {
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    v___x_1571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__4,
    );
    v___x_1572_ = lean_alloc_closure(
        l_Lean_Parser_many1_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1572_, 0, v___x_1571_);
    return v___x_1572_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_parenthesizer___closed__6() -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__5,
    );
    v___x_1574_ = l_Lean_Parser_Level_max_parenthesizer___closed__1;
    v___x_1575_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1575_, 0, v___x_1574_);
    lean_closure_set(v___x_1575_, 1, v___x_1573_);
    return v___x_1575_;
}
pub unsafe fn _init_l_Lean_Parser_Level_max_parenthesizer___closed__7() -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__6_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__6,
    );
    v___x_1577_ = lean_unsigned_to_nat(1024);
    v___x_1578_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1579_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1579_, 0, v___x_1578_);
    lean_closure_set(v___x_1579_, 1, v___x_1577_);
    lean_closure_set(v___x_1579_, 2, v___x_1576_);
    return v___x_1579_;
}
pub unsafe fn l_Lean_Parser_Level_max_parenthesizer(
    mut v_a_1580_: *mut LeanObject,
    mut v_a_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
    mut v_a_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Lean_Parser_Level_max_parenthesizer___closed__0;
    v___x_1586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__7_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__7,
    );
    v___x_1587_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1585_,
        v___x_1586_,
        v_a_1580_,
        v_a_1581_,
        v_a_1582_,
        v_a_1583_,
    );
    return v___x_1587_;
}
pub unsafe fn l_Lean_Parser_Level_max_parenthesizer___boxed(
    mut v_a_1588_: *mut LeanObject,
    mut v_a_1589_: *mut LeanObject,
    mut v_a_1590_: *mut LeanObject,
    mut v_a_1591_: *mut LeanObject,
    mut v_a_1592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1593_: *mut LeanObject = core::ptr::null_mut();
    v_res_1593_ = l_Lean_Parser_Level_max_parenthesizer(v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_);
    lean_dec(v_a_1591_);
    lean_dec_ref(v_a_1590_);
    lean_dec(v_a_1589_);
    lean_dec_ref(v_a_1588_);
    return v_res_1593_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1602_ = l_Lean_Parser_Level_max___closed__1;
    v___x_1603_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___closed__0;
    v___x_1604_ = lean_alloc_closure(
        l_Lean_Parser_Level_max_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1605_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1601_,
        v___x_1602_,
        v___x_1603_,
        v___x_1604_,
    );
    return v___x_1605_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11___boxed(
    mut v_a_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1607_: *mut LeanObject = core::ptr::null_mut();
    v_res_1607_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
    return v_res_1607_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__2() -> *mut LeanObject {
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = 0;
    v___x_1615_ = 1;
    v___x_1616_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1617_ = l_Lean_Parser_Level_imax___closed__0;
    v___x_1618_ = l_Lean_Parser_mkAntiquot(v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
    return v___x_1618_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__3() -> *mut LeanObject {
    let mut v___x_1619_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1619_ = 1;
    v___x_1620_ = l_Lean_Parser_Level_imax___closed__0;
    v___x_1621_ = l_Lean_Parser_nonReservedSymbol(v___x_1620_, v___x_1619_);
    return v___x_1621_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__4() -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max___closed__6_once),
        _init_l_Lean_Parser_Level_max___closed__6,
    );
    v___x_1623_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__3_once),
        _init_l_Lean_Parser_Level_imax___closed__3,
    );
    v___x_1624_ = l_Lean_Parser_andthen(v___x_1623_, v___x_1622_);
    return v___x_1624_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__5() -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__4_once),
        _init_l_Lean_Parser_Level_imax___closed__4,
    );
    v___x_1626_ = lean_unsigned_to_nat(1024);
    v___x_1627_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1628_ = l_Lean_Parser_leadingNode(v___x_1627_, v___x_1626_, v___x_1625_);
    return v___x_1628_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__6() -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__5_once),
        _init_l_Lean_Parser_Level_imax___closed__5,
    );
    v___x_1630_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__2_once),
        _init_l_Lean_Parser_Level_imax___closed__2,
    );
    v___x_1631_ = l_Lean_Parser_withAntiquot(v___x_1630_, v___x_1629_);
    return v___x_1631_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax___closed__7() -> *mut LeanObject {
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1632_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__6_once),
        _init_l_Lean_Parser_Level_imax___closed__6,
    );
    v___x_1633_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1634_ = l_Lean_Parser_withCache(v___x_1633_, v___x_1632_);
    return v___x_1634_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax() -> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax___closed__7_once),
        _init_l_Lean_Parser_Level_imax___closed__7,
    );
    return v___x_1635_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1()
-> *mut LeanObject {
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1638_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1639_ = l_Lean_Parser_Level_imax;
    v___x_1640_ = lean_unsigned_to_nat(1000);
    v___x_1641_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1637_, v___x_1638_, v___x_1639_, v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1___boxed(
    mut v_a_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1643_: *mut LeanObject = core::ptr::null_mut();
    v_res_1643_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
    return v_res_1643_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3()
-> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1670_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___closed__6;
    v___x_1671_ = l_Lean_addBuiltinDeclarationRanges(v___x_1669_, v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3___boxed(
    mut v_a_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1673_: *mut LeanObject = core::ptr::null_mut();
    v_res_1673_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
    return v_res_1673_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    v___x_1685_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_formatter___closed__5_once),
        _init_l_Lean_Parser_Level_max_formatter___closed__5,
    );
    v___x_1686_ = l_Lean_Parser_Level_imax_formatter___closed__1;
    v___x_1687_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1687_, 0, v___x_1686_);
    lean_closure_set(v___x_1687_, 1, v___x_1685_);
    return v___x_1687_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1688_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_formatter___closed__2_once),
        _init_l_Lean_Parser_Level_imax_formatter___closed__2,
    );
    v___x_1689_ = lean_unsigned_to_nat(1024);
    v___x_1690_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1691_ = lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1691_, 0, v___x_1690_);
    lean_closure_set(v___x_1691_, 1, v___x_1689_);
    lean_closure_set(v___x_1691_, 2, v___x_1688_);
    return v___x_1691_;
}
pub unsafe fn l_Lean_Parser_Level_imax_formatter(
    mut v_a_1692_: *mut LeanObject,
    mut v_a_1693_: *mut LeanObject,
    mut v_a_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1697_ = l_Lean_Parser_Level_imax_formatter___closed__0;
    v___x_1698_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_formatter___closed__3_once),
        _init_l_Lean_Parser_Level_imax_formatter___closed__3,
    );
    v___x_1699_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1697_,
        v___x_1698_,
        v_a_1692_,
        v_a_1693_,
        v_a_1694_,
        v_a_1695_,
    );
    return v___x_1699_;
}
pub unsafe fn l_Lean_Parser_Level_imax_formatter___boxed(
    mut v_a_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
    mut v_a_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1705_: *mut LeanObject = core::ptr::null_mut();
    v_res_1705_ = l_Lean_Parser_Level_imax_formatter(v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
    lean_dec(v_a_1703_);
    lean_dec_ref(v_a_1702_);
    lean_dec(v_a_1701_);
    lean_dec_ref(v_a_1700_);
    return v_res_1705_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7()
-> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1714_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1715_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___closed__0;
    v___x_1716_ = lean_alloc_closure(
        l_Lean_Parser_Level_imax_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1717_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1713_,
        v___x_1714_,
        v___x_1715_,
        v___x_1716_,
    );
    return v___x_1717_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7___boxed(
    mut v_a_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_res_1719_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
    return v_res_1719_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    v___x_1731_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_max_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Level_max_parenthesizer___closed__5,
    );
    v___x_1732_ = l_Lean_Parser_Level_imax_parenthesizer___closed__1;
    v___x_1733_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_1733_, 0, v___x_1732_);
    lean_closure_set(v___x_1733_, 1, v___x_1731_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Level_imax_parenthesizer___closed__2,
    );
    v___x_1735_ = lean_unsigned_to_nat(1024);
    v___x_1736_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1737_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_1737_, 0, v___x_1736_);
    lean_closure_set(v___x_1737_, 1, v___x_1735_);
    lean_closure_set(v___x_1737_, 2, v___x_1734_);
    return v___x_1737_;
}
pub unsafe fn l_Lean_Parser_Level_imax_parenthesizer(
    mut v_a_1738_: *mut LeanObject,
    mut v_a_1739_: *mut LeanObject,
    mut v_a_1740_: *mut LeanObject,
    mut v_a_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Lean_Parser_Level_imax_parenthesizer___closed__0;
    v___x_1744_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_imax_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Level_imax_parenthesizer___closed__3,
    );
    v___x_1745_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1743_,
        v___x_1744_,
        v_a_1738_,
        v_a_1739_,
        v_a_1740_,
        v_a_1741_,
    );
    return v___x_1745_;
}
pub unsafe fn l_Lean_Parser_Level_imax_parenthesizer___boxed(
    mut v_a_1746_: *mut LeanObject,
    mut v_a_1747_: *mut LeanObject,
    mut v_a_1748_: *mut LeanObject,
    mut v_a_1749_: *mut LeanObject,
    mut v_a_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1751_: *mut LeanObject = core::ptr::null_mut();
    v_res_1751_ =
        l_Lean_Parser_Level_imax_parenthesizer(v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
    lean_dec(v_a_1749_);
    lean_dec_ref(v_a_1748_);
    lean_dec(v_a_1747_);
    lean_dec_ref(v_a_1746_);
    return v_res_1751_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1760_ = l_Lean_Parser_Level_imax___closed__1;
    v___x_1761_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___closed__0;
    v___x_1762_ = lean_alloc_closure(
        l_Lean_Parser_Level_imax_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1759_,
        v___x_1760_,
        v___x_1761_,
        v___x_1762_,
    );
    return v___x_1763_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11___boxed(
    mut v_a_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1765_: *mut LeanObject = core::ptr::null_mut();
    v_res_1765_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
    return v_res_1765_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole___closed__2() -> *mut LeanObject {
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: u8 = 0;
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_1772_ = 0;
    v___x_1773_ = 1;
    v___x_1774_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1775_ = l_Lean_Parser_Level_hole___closed__0;
    v___x_1776_ = l_Lean_Parser_mkAntiquot(v___x_1775_, v___x_1774_, v___x_1773_, v___x_1772_);
    return v___x_1776_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole___closed__4() -> *mut LeanObject {
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v___x_1778_ = l_Lean_Parser_Level_hole___closed__3;
    v___x_1779_ = l_Lean_Parser_symbol(v___x_1778_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole___closed__5() -> *mut LeanObject {
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__4_once),
        _init_l_Lean_Parser_Level_hole___closed__4,
    );
    v___x_1781_ = lean_unsigned_to_nat(1024);
    v___x_1782_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1783_ = l_Lean_Parser_leadingNode(v___x_1782_, v___x_1781_, v___x_1780_);
    return v___x_1783_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole___closed__6() -> *mut LeanObject {
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    v___x_1784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__5_once),
        _init_l_Lean_Parser_Level_hole___closed__5,
    );
    v___x_1785_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__2_once),
        _init_l_Lean_Parser_Level_hole___closed__2,
    );
    v___x_1786_ = l_Lean_Parser_withAntiquot(v___x_1785_, v___x_1784_);
    return v___x_1786_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole___closed__7() -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    v___x_1787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__6_once),
        _init_l_Lean_Parser_Level_hole___closed__6,
    );
    v___x_1788_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1789_ = l_Lean_Parser_withCache(v___x_1788_, v___x_1787_);
    return v___x_1789_;
}
pub unsafe fn _init_l_Lean_Parser_Level_hole() -> *mut LeanObject {
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    v___x_1790_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_hole___closed__7_once),
        _init_l_Lean_Parser_Level_hole___closed__7,
    );
    return v___x_1790_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1()
-> *mut LeanObject {
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1793_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1794_ = l_Lean_Parser_Level_hole;
    v___x_1795_ = lean_unsigned_to_nat(1000);
    v___x_1796_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1792_, v___x_1793_, v___x_1794_, v___x_1795_);
    return v___x_1796_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1___boxed(
    mut v_a_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
    return v_res_1798_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3()
-> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1826_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___closed__6;
    v___x_1827_ = l_Lean_addBuiltinDeclarationRanges(v___x_1825_, v___x_1826_);
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3___boxed(
    mut v_a_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_res_1829_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
    return v_res_1829_;
}
pub unsafe fn l_Lean_Parser_Level_hole_formatter(
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ = l_Lean_Parser_Level_hole_formatter___closed__0;
    v___x_1849_ = l_Lean_Parser_Level_hole_formatter___closed__2;
    v___x_1850_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_1848_,
        v___x_1849_,
        v_a_1843_,
        v_a_1844_,
        v_a_1845_,
        v_a_1846_,
    );
    return v___x_1850_;
}
pub unsafe fn l_Lean_Parser_Level_hole_formatter___boxed(
    mut v_a_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_Parser_Level_hole_formatter(v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
    lean_dec(v_a_1854_);
    lean_dec_ref(v_a_1853_);
    lean_dec(v_a_1852_);
    lean_dec_ref(v_a_1851_);
    return v_res_1856_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7()
-> *mut LeanObject {
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v___x_1864_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_1865_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1866_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___closed__0;
    v___x_1867_ = lean_alloc_closure(
        l_Lean_Parser_Level_hole_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1868_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1864_,
        v___x_1865_,
        v___x_1866_,
        v___x_1867_,
    );
    return v___x_1868_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7___boxed(
    mut v_a_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1870_: *mut LeanObject = core::ptr::null_mut();
    v_res_1870_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
    return v_res_1870_;
}
pub unsafe fn l_Lean_Parser_Level_hole_parenthesizer(
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_Lean_Parser_Level_hole_parenthesizer___closed__0;
    v___x_1890_ = l_Lean_Parser_Level_hole_parenthesizer___closed__2;
    v___x_1891_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_1889_,
        v___x_1890_,
        v_a_1884_,
        v_a_1885_,
        v_a_1886_,
        v_a_1887_,
    );
    return v___x_1891_;
}
pub unsafe fn l_Lean_Parser_Level_hole_parenthesizer___boxed(
    mut v_a_1892_: *mut LeanObject,
    mut v_a_1893_: *mut LeanObject,
    mut v_a_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ =
        l_Lean_Parser_Level_hole_parenthesizer(v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
    lean_dec(v_a_1895_);
    lean_dec_ref(v_a_1894_);
    lean_dec(v_a_1893_);
    lean_dec_ref(v_a_1892_);
    return v_res_1897_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_1906_ = l_Lean_Parser_Level_hole___closed__1;
    v___x_1907_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___closed__0;
    v___x_1908_ = lean_alloc_closure(
        l_Lean_Parser_Level_hole_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1909_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1905_,
        v___x_1906_,
        v___x_1907_,
        v___x_1908_,
    );
    return v___x_1909_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11___boxed(
    mut v_a_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1911_: *mut LeanObject = core::ptr::null_mut();
    v_res_1911_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
    return v_res_1911_;
}
pub unsafe fn _init_l_Lean_Parser_Level_num___closed__0() -> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_Parser_maxPrec;
    v___x_1913_ = l_Lean_Parser_checkPrec(v___x_1912_);
    return v___x_1913_;
}
pub unsafe fn _init_l_Lean_Parser_Level_num___closed__1() -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_Parser_numLit;
    v___x_1915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__0_once),
        _init_l_Lean_Parser_Level_num___closed__0,
    );
    v___x_1916_ = l_Lean_Parser_andthen(v___x_1915_, v___x_1914_);
    return v___x_1916_;
}
pub unsafe fn _init_l_Lean_Parser_Level_num() -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__1_once),
        _init_l_Lean_Parser_Level_num___closed__1,
    );
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1()
-> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = l_Lean_Parser_levelParser___closed__0;
    v___x_1926_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1;
    v___x_1927_ = l_Lean_Parser_Level_num;
    v___x_1928_ = lean_unsigned_to_nat(1000);
    v___x_1929_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_1925_, v___x_1926_, v___x_1927_, v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___boxed(
    mut v_a_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1931_: *mut LeanObject = core::ptr::null_mut();
    v_res_1931_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
    return v_res_1931_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3()
-> *mut LeanObject {
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    v___x_1956_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1___closed__1;
    v___x_1957_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___closed__6;
    v___x_1958_ = l_Lean_addBuiltinDeclarationRanges(v___x_1956_, v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3___boxed(
    mut v_a_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1960_: *mut LeanObject = core::ptr::null_mut();
    v_res_1960_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
    return v_res_1960_;
}
pub unsafe fn l_Lean_Parser_Level_num_formatter(
    mut v_a_1962_: *mut LeanObject,
    mut v_a_1963_: *mut LeanObject,
    mut v_a_1964_: *mut LeanObject,
    mut v_a_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    v___x_1967_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_1968_ = l_Lean_Parser_Level_num_formatter___closed__0;
    v___x_1969_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___x_1967_,
        v___x_1968_,
        v_a_1962_,
        v_a_1963_,
        v_a_1964_,
        v_a_1965_,
    );
    return v___x_1969_;
}
pub unsafe fn l_Lean_Parser_Level_num_formatter___boxed(
    mut v_a_1970_: *mut LeanObject,
    mut v_a_1971_: *mut LeanObject,
    mut v_a_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lean_Parser_Level_num_formatter(v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
    lean_dec(v_a_1973_);
    lean_dec_ref(v_a_1972_);
    lean_dec(v_a_1971_);
    lean_dec_ref(v_a_1970_);
    return v_res_1975_;
}
pub unsafe fn l_Lean_Parser_Level_num_parenthesizer___lam__0(
    mut v___x_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    v___x_1982_ =
        l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_1976_, v___y_1978_);
    return v___x_1982_;
}
pub unsafe fn l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed(
    mut v___x_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1989_: *mut LeanObject = core::ptr::null_mut();
    v_res_1989_ = l_Lean_Parser_Level_num_parenthesizer___lam__0(
        v___x_1983_,
        v___y_1984_,
        v___y_1985_,
        v___y_1986_,
        v___y_1987_,
    );
    lean_dec(v___y_1987_);
    lean_dec_ref(v___y_1986_);
    lean_dec(v___y_1985_);
    lean_dec_ref(v___y_1984_);
    return v_res_1989_;
}
pub unsafe fn _init_l_Lean_Parser_Level_num_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1991_: *mut LeanObject = core::ptr::null_mut();
    v___x_1990_ = l_Lean_Parser_maxPrec;
    v___f_1991_ = lean_alloc_closure(
        l_Lean_Parser_Level_num_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1991_, 0, v___x_1990_);
    return v___f_1991_;
}
pub unsafe fn l_Lean_Parser_Level_num_parenthesizer(
    mut v_a_1993_: *mut LeanObject,
    mut v_a_1994_: *mut LeanObject,
    mut v_a_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___f_1998_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num_parenthesizer___closed__0_once),
        _init_l_Lean_Parser_Level_num_parenthesizer___closed__0,
    );
    v___x_1999_ = l_Lean_Parser_Level_num_parenthesizer___closed__1;
    v___x_2000_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___f_1998_,
        v___x_1999_,
        v_a_1993_,
        v_a_1994_,
        v_a_1995_,
        v_a_1996_,
    );
    return v___x_2000_;
}
pub unsafe fn l_Lean_Parser_Level_num_parenthesizer___boxed(
    mut v_a_2001_: *mut LeanObject,
    mut v_a_2002_: *mut LeanObject,
    mut v_a_2003_: *mut LeanObject,
    mut v_a_2004_: *mut LeanObject,
    mut v_a_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2006_: *mut LeanObject = core::ptr::null_mut();
    v_res_2006_ = l_Lean_Parser_Level_num_parenthesizer(v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
    lean_dec(v_a_2004_);
    lean_dec_ref(v_a_2003_);
    lean_dec(v_a_2002_);
    lean_dec_ref(v_a_2001_);
    return v_res_2006_;
}
pub unsafe fn _init_l_Lean_Parser_Level_ident___closed__0() -> *mut LeanObject {
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2007_ = l_Lean_Parser_ident;
    v___x_2008_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num___closed__0_once),
        _init_l_Lean_Parser_Level_num___closed__0,
    );
    v___x_2009_ = l_Lean_Parser_andthen(v___x_2008_, v___x_2007_);
    return v___x_2009_;
}
pub unsafe fn _init_l_Lean_Parser_Level_ident() -> *mut LeanObject {
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    v___x_2010_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_ident___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_ident___closed__0_once),
        _init_l_Lean_Parser_Level_ident___closed__0,
    );
    return v___x_2010_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1()
-> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l_Lean_Parser_levelParser___closed__0;
    v___x_2019_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1;
    v___x_2020_ = l_Lean_Parser_Level_ident;
    v___x_2021_ = lean_unsigned_to_nat(1000);
    v___x_2022_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2018_, v___x_2019_, v___x_2020_, v___x_2021_);
    return v___x_2022_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___boxed(
    mut v_a_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2024_: *mut LeanObject = core::ptr::null_mut();
    v_res_2024_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
    return v_res_2024_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3()
-> *mut LeanObject {
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    v___x_2051_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1___closed__1;
    v___x_2052_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___closed__6;
    v___x_2053_ = l_Lean_addBuiltinDeclarationRanges(v___x_2051_, v___x_2052_);
    return v___x_2053_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3___boxed(
    mut v_a_2054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2055_: *mut LeanObject = core::ptr::null_mut();
    v_res_2055_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
    return v_res_2055_;
}
pub unsafe fn l_Lean_Parser_Level_ident_formatter(
    mut v_a_2057_: *mut LeanObject,
    mut v_a_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v___x_2062_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2063_ = l_Lean_Parser_Level_ident_formatter___closed__0;
    v___x_2064_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___x_2062_,
        v___x_2063_,
        v_a_2057_,
        v_a_2058_,
        v_a_2059_,
        v_a_2060_,
    );
    return v___x_2064_;
}
pub unsafe fn l_Lean_Parser_Level_ident_formatter___boxed(
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lean_Parser_Level_ident_formatter(v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
    lean_dec(v_a_2068_);
    lean_dec_ref(v_a_2067_);
    lean_dec(v_a_2066_);
    lean_dec_ref(v_a_2065_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_Parser_Level_ident_parenthesizer(
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    v___f_2077_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_num_parenthesizer___closed__0_once),
        _init_l_Lean_Parser_Level_num_parenthesizer___closed__0,
    );
    v___x_2078_ = l_Lean_Parser_Level_ident_parenthesizer___closed__0;
    v___x_2079_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___f_2077_,
        v___x_2078_,
        v_a_2072_,
        v_a_2073_,
        v_a_2074_,
        v_a_2075_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Lean_Parser_Level_ident_parenthesizer___boxed(
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2085_: *mut LeanObject = core::ptr::null_mut();
    v_res_2085_ =
        l_Lean_Parser_Level_ident_parenthesizer(v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
    lean_dec(v_a_2083_);
    lean_dec_ref(v_a_2082_);
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    return v_res_2085_;
}
pub unsafe fn _init_l_Lean_Parser_Level_addLit___closed__3() -> *mut LeanObject {
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    v___x_2093_ = l_Lean_Parser_Level_addLit___closed__2;
    v___x_2094_ = l_Lean_Parser_symbol(v___x_2093_);
    return v___x_2094_;
}
pub unsafe fn _init_l_Lean_Parser_Level_addLit___closed__4() -> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_Parser_numLit;
    v___x_2096_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__3_once),
        _init_l_Lean_Parser_Level_addLit___closed__3,
    );
    v___x_2097_ = l_Lean_Parser_andthen(v___x_2096_, v___x_2095_);
    return v___x_2097_;
}
pub unsafe fn _init_l_Lean_Parser_Level_addLit___closed__5() -> *mut LeanObject {
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    v___x_2098_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__4_once),
        _init_l_Lean_Parser_Level_addLit___closed__4,
    );
    v___x_2099_ = lean_unsigned_to_nat(0);
    v___x_2100_ = lean_unsigned_to_nat(65);
    v___x_2101_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2102_ = l_Lean_Parser_trailingNode(v___x_2101_, v___x_2100_, v___x_2099_, v___x_2098_);
    return v___x_2102_;
}
pub unsafe fn _init_l_Lean_Parser_Level_addLit() -> *mut LeanObject {
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    v___x_2103_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Level_addLit___closed__5_once),
        _init_l_Lean_Parser_Level_addLit___closed__5,
    );
    return v___x_2103_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1()
-> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    v___x_2105_ = l_Lean_Parser_levelParser___closed__0;
    v___x_2106_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2107_ = l_Lean_Parser_Level_addLit;
    v___x_2108_ = lean_unsigned_to_nat(1000);
    v___x_2109_ =
        l_Lean_Parser_addBuiltinTrailingParser(v___x_2105_, v___x_2106_, v___x_2107_, v___x_2108_);
    return v___x_2109_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1___boxed(
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
    return v_res_2111_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3()
-> *mut LeanObject {
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    v___x_2138_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2139_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___closed__6;
    v___x_2140_ = l_Lean_addBuiltinDeclarationRanges(v___x_2138_, v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3___boxed(
    mut v_a_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2142_: *mut LeanObject = core::ptr::null_mut();
    v_res_2142_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
    return v_res_2142_;
}
pub unsafe fn l_Lean_Parser_Level_addLit_formatter(
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    v___x_2153_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2154_ = l_Lean_Parser_Level_addLit_formatter___closed__1;
    v___x_2155_ = l_Lean_PrettyPrinter_Formatter_trailingNode_formatter___redArg(
        v___x_2153_,
        v___x_2154_,
        v_a_2148_,
        v_a_2149_,
        v_a_2150_,
        v_a_2151_,
    );
    return v___x_2155_;
}
pub unsafe fn l_Lean_Parser_Level_addLit_formatter___boxed(
    mut v_a_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_a_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Lean_Parser_Level_addLit_formatter(v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
    lean_dec(v_a_2159_);
    lean_dec_ref(v_a_2158_);
    lean_dec(v_a_2157_);
    lean_dec_ref(v_a_2156_);
    return v_res_2161_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7()
-> *mut LeanObject {
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    v___x_2169_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_2170_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2171_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___closed__0;
    v___x_2172_ = lean_alloc_closure(
        l_Lean_Parser_Level_addLit_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2173_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2169_,
        v___x_2170_,
        v___x_2171_,
        v___x_2172_,
    );
    return v___x_2173_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7___boxed(
    mut v_a_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2175_: *mut LeanObject = core::ptr::null_mut();
    v_res_2175_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
    return v_res_2175_;
}
pub unsafe fn l_Lean_Parser_Level_addLit_parenthesizer(
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2186_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2187_ = lean_unsigned_to_nat(65);
    v___x_2188_ = lean_unsigned_to_nat(0);
    v___x_2189_ = l_Lean_Parser_Level_addLit_parenthesizer___closed__1;
    v___x_2190_ = l_Lean_PrettyPrinter_Parenthesizer_trailingNode_parenthesizer(
        v___x_2186_,
        v___x_2187_,
        v___x_2188_,
        v___x_2189_,
        v_a_2181_,
        v_a_2182_,
        v_a_2183_,
        v_a_2184_,
    );
    return v___x_2190_;
}
pub unsafe fn l_Lean_Parser_Level_addLit_parenthesizer___boxed(
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2196_: *mut LeanObject = core::ptr::null_mut();
    v_res_2196_ =
        l_Lean_Parser_Level_addLit_parenthesizer(v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
    lean_dec(v_a_2194_);
    lean_dec_ref(v_a_2193_);
    lean_dec(v_a_2192_);
    lean_dec_ref(v_a_2191_);
    return v_res_2196_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2204_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2205_ = l_Lean_Parser_Level_addLit___closed__1;
    v___x_2206_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___closed__0;
    v___x_2207_ = lean_alloc_closure(
        l_Lean_Parser_Level_addLit_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2208_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2204_,
        v___x_2205_,
        v___x_2206_,
        v___x_2207_,
    );
    return v___x_2208_;
}
pub unsafe fn l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11___boxed(
    mut v_a_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2210_: *mut LeanObject = core::ptr::null_mut();
    v_res_2210_ = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
    return v_res_2210_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Level(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_initFn_00___x40_Lean_Parser_Level_2271617841____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_paren = _init_l_Lean_Parser_Level_paren();
    lean_mark_persistent(l_Lean_Parser_Level_paren);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_formatter__9();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_paren___regBuiltin_Lean_Parser_Level_paren_parenthesizer__15();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_max = _init_l_Lean_Parser_Level_max();
    lean_mark_persistent(l_Lean_Parser_Level_max);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_max___regBuiltin_Lean_Parser_Level_max_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_imax = _init_l_Lean_Parser_Level_imax();
    lean_mark_persistent(l_Lean_Parser_Level_imax);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_imax___regBuiltin_Lean_Parser_Level_imax_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_hole = _init_l_Lean_Parser_Level_hole();
    lean_mark_persistent(l_Lean_Parser_Level_hole);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_hole___regBuiltin_Lean_Parser_Level_hole_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_num = _init_l_Lean_Parser_Level_num();
    lean_mark_persistent(l_Lean_Parser_Level_num);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_num___regBuiltin_Lean_Parser_Level_num_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_ident = _init_l_Lean_Parser_Level_ident();
    lean_mark_persistent(l_Lean_Parser_Level_ident);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_ident___regBuiltin_Lean_Parser_Level_ident_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Level_addLit = _init_l_Lean_Parser_Level_addLit();
    lean_mark_persistent(l_Lean_Parser_Level_addLit);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Level_0__Lean_Parser_Level_addLit___regBuiltin_Lean_Parser_Level_addLit_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Level(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Level(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Level(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser_Level(builtin);
}
