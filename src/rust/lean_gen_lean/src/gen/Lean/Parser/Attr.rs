// Lean compiler output
// Module: Lean.Parser.Attr
// Imports: Lean.Parser.Extra
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Parser::Basic::{
    l_Lean_Parser_andthen, l_Lean_Parser_categoryParser, l_Lean_Parser_checkPrec,
    l_Lean_Parser_leadingNode, l_Lean_Parser_mkAntiquot, l_Lean_Parser_nonReservedSymbol,
    l_Lean_Parser_orelse, l_Lean_Parser_skip, l_Lean_Parser_symbol, l_Lean_Parser_withAntiquot,
};
use crate::r#gen::Lean::Parser::Extension::{
    l_Lean_Parser_addBuiltinLeadingParser, l_Lean_Parser_registerBuiltinDynamicParserAttribute,
    l_Lean_Parser_registerBuiltinParserAttribute,
};
use crate::r#gen::Lean::Parser::Extra::{
    initialize_Lean_Parser_Extra, l_Lean_Parser_ident, l_Lean_Parser_ident_formatter___boxed,
    l_Lean_Parser_ident_parenthesizer___boxed, l_Lean_Parser_leadingNode_formatter___boxed,
    l_Lean_Parser_many, l_Lean_Parser_many_formatter___boxed,
    l_Lean_Parser_many_parenthesizer___boxed, l_Lean_Parser_many1,
    l_Lean_Parser_many1_formatter___boxed, l_Lean_Parser_many1_parenthesizer___boxed,
    l_Lean_Parser_mkAntiquot_formatter___boxed, l_Lean_Parser_mkAntiquot_parenthesizer___boxed,
    l_Lean_Parser_nonReservedSymbol_formatter___boxed,
    l_Lean_Parser_nonReservedSymbol_parenthesizer___boxed, l_Lean_Parser_numLit,
    l_Lean_Parser_numLit_formatter___boxed, l_Lean_Parser_numLit_parenthesizer___boxed,
    l_Lean_Parser_optional, l_Lean_Parser_optional_formatter___boxed,
    l_Lean_Parser_optional_parenthesizer___boxed, l_Lean_Parser_ppSpace_parenthesizer___boxed,
    l_Lean_Parser_strLit, l_Lean_Parser_strLit_formatter___boxed,
    l_Lean_Parser_strLit_parenthesizer___boxed, l_Lean_Parser_symbol_formatter___boxed,
    l_Lean_Parser_symbol_parenthesizer___boxed, runtime_initialize_Lean_Parser_Extra,
};
use crate::r#gen::Lean::Parser::Types::{l_Lean_Parser_maxPrec, l_Lean_Parser_withCache};
use crate::r#gen::Lean::PrettyPrinter::Formatter::{
    l_Lean_PrettyPrinter_Formatter_andthen_formatter,
    l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_categoryParser_formatter,
    l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter,
    l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed,
    l_Lean_PrettyPrinter_Formatter_pushLine___redArg, l_Lean_PrettyPrinter_formatterAttribute,
};
use crate::r#gen::Lean::PrettyPrinter::Parenthesizer::{
    l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer,
    l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed,
    l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer,
    l_Lean_PrettyPrinter_parenthesizerAttribute,
};
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 112, 114, 105, 111, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9344938725912493582 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 97, 116, 101, 103, 111, 114, 121, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 105, 111, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11615938313939332388 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12953954729981012753 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6386160366488538211 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16903608221218324827 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14144577819487878630 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12820864901300304239 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4627047623736319178 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18332721513354491535 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9870152696988459514 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14377136827182876443 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5381815324804079886 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11112453953516691050 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1857506627 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1564673465549365540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12807883410376724107 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2138206098876806091 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2134880034630724318 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 114, 105, 111, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2249309967286780005 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17836958171642591098 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 97, 116, 116, 114, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14167642945230817130 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11615938313939332388 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9016880043843696902 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 249558774 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,3781160332249273827 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11530201504022192696 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14597782152571136476 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9524778246848127557 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 116, 116, 114, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2890506875127363237 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6289677862665402693 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Priority_numPrio___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Priority_numPrio___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Priority_numPrio___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Priority_numPrio___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Priority_numPrio: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 114, 105, 111, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 117, 109, 80, 114, 105, 111, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value) as *mut crate::leanh::LeanObject,5288000119911482163 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value) as *mut crate::leanh::LeanObject,11264383648239794238 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 66 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 66 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Priority_numPrio_formatter___closed__0_value:
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
static mut l_Lean_Parser_Priority_numPrio_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value:
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
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 105, 109, 112, 108, 101, 0],
    };
static mut l_Lean_Parser_Attr_simple___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_simple___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_simple___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_simple___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_simple___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3878072352281346923 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_simple___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_simple___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simple: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 113 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 113 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_Attr_simple_formatter___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
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
static mut l_Lean_Parser_Attr_simple_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__3_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Parser_priorityParser_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__4_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__5_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__6_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__7_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__8_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_formatter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,6120378905460204942 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value:
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
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value:
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
    m_fun: l_Lean_Parser_ppSpace_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value:
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
    m_fun: l_Lean_Parser_priorityParser_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value:
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
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut crate::leanh::LeanObject,3878072352281346923 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,7229047310583692226 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [109, 97, 99, 114, 111, 0],
    };
static mut l_Lean_Parser_Attr_macro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_macro___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_macro___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_macro___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_macro___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5370970300127562257 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_macro___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_macro___closed__3_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [109, 97, 99, 114, 111, 32, 0],
    };
static mut l_Lean_Parser_Attr_macro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_macro___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_macro___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_macro: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 73 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 73 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__3_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut crate::leanh::LeanObject,5370970300127562257 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,18431002086242330140 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut crate::leanh::LeanObject,5370970300127562257 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,11655949949594088000 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [101, 120, 112, 111, 114, 116, 0],
    };
static mut l_Lean_Parser_Attr_export___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_export___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_export___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_export___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_export___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8336882369266271787 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_export___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_export___closed__3_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [101, 120, 112, 111, 114, 116, 32, 0],
    };
static mut l_Lean_Parser_Attr_export___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_export___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_export___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_export: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 74 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 74 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__3_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut crate::leanh::LeanObject,8336882369266271787 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,17544970176348460878 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut crate::leanh::LeanObject,8336882369266271787 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,17081142296450615810 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [114, 101, 99, 117, 114, 115, 111, 114, 0],
    };
static mut l_Lean_Parser_Attr_recursor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_recursor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6133751819545484634 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_recursor___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_recursor___closed__3_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [114, 101, 99, 117, 114, 115, 111, 114, 32, 0],
    };
static mut l_Lean_Parser_Attr_recursor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_recursor___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_recursor___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_recursor: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 101 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 101 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut crate::leanh::LeanObject,6133751819545484634 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,932075812504011379 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut crate::leanh::LeanObject,6133751819545484634 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,17060214783765589863 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [99, 108, 97, 115, 115, 0],
    };
static mut l_Lean_Parser_Attr_class___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_class___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_class___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_class___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_class___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
                as *mut crate::leanh::LeanObject,
            4629983612007222933 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_class___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_class___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_class___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_class___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_class___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_class___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_class: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 69 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 69 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__2_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut crate::leanh::LeanObject,4629983612007222933 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,13536653989562982728 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut crate::leanh::LeanObject,4629983612007222933 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,10517532522357765908 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0],
    };
static mut l_Lean_Parser_Attr_instance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_instance___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_instance___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_instance___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_instance___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            12927425362287788416 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_instance___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_instance___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_instance: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 112 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 112 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut crate::leanh::LeanObject,12927425362287788416 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,15262820364925198721 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut crate::leanh::LeanObject,12927425362287788416 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,8038967186449509541 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance___closed__0_value: crate::leanh::LeanStringObject<
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
        100, 101, 102, 97, 117, 108, 116, 95, 105, 110, 115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_Parser_Attr_default__instance___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_default__instance___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8421805314306529249 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_default__instance___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_default__instance___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_default__instance: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 138 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 138 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value) as *mut crate::leanh::LeanObject,8421805314306529249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,7711090014203637900 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value) as *mut crate::leanh::LeanObject,8421805314306529249 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,652804362000181872 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Parser_Attr_specialize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_specialize___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
                as *mut crate::leanh::LeanObject,
            3770768959921593381 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_specialize___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_specialize___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_specialize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 134 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 134 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__2_value:
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
    m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__4_value:
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
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut crate::leanh::LeanObject,3770768959921593381 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,13290341165972871288 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value:
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
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value:
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
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut crate::leanh::LeanObject,3770768959921593381 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,10108530158295159428 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [101, 120, 116, 101, 114, 110, 69, 110, 116, 114, 121, 0],
    };
static mut l_Lean_Parser_Attr_externEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_externEntry___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13020966400515078259 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_externEntry___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_externEntry___closed__5_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [105, 110, 108, 105, 110, 101, 32, 0],
    };
static mut l_Lean_Parser_Attr_externEntry___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_externEntry___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_externEntry___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_externEntry: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Attr_extern___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [101, 120, 116, 101, 114, 110, 0],
    };
static mut l_Lean_Parser_Attr_extern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_extern___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_extern___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_extern___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_extern___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8121184350197546670 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_extern___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_extern: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 93 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 93 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__5_value:
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
    m_fun: l_Lean_Parser_strLit_formatter___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut crate::leanh::LeanObject,13020966400515078259 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,16958419729801073126 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extern_formatter___closed__0_value: crate::leanh::LeanClosureObject<
    4,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extern_formatter___closed__1_value: crate::leanh::LeanClosureObject<
    2,
> = crate::leanh::LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_extern_formatter___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut crate::leanh::LeanObject,8121184350197546670 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,17978558652694071311 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value:
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
    m_fun: l_Lean_Parser_strLit_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut crate::leanh::LeanObject,13020966400515078259 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,13755836315023133898 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut crate::leanh::LeanObject,8121184350197546670 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,5066783692093791339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 97, 99, 116, 105, 99, 95, 97, 108, 116, 0],
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_tactic__alt___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7294395221027647453 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_tactic__alt___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__alt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value: crate::leanh::LeanStringObject<209> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 209, m_capacity: 209, m_length: 208, m_data: [68, 101, 99, 108, 97, 114, 101, 115, 32, 116, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32, 116, 111, 32, 98, 101, 32, 97, 110, 32, 97, 108, 105, 97, 115, 32, 111, 114, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 102, 111, 114, 109, 32, 111, 102, 32, 97, 110, 32, 101, 120, 105, 115, 116, 105, 110, 103, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 84, 104, 105, 115, 32, 104, 97, 115, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 102, 102, 101, 99, 116, 115, 58, 10, 42, 32, 84, 104, 101, 32, 97, 108, 105, 97, 115, 32, 114, 101, 108, 97, 116, 105, 111, 110, 115, 104, 105, 112, 32, 105, 115, 32, 115, 97, 118, 101, 100, 10, 42, 32, 84, 104, 101, 32, 100, 111, 99, 115, 116, 114, 105, 110, 103, 32, 105, 115, 32, 116, 97, 107, 101, 110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 111, 114, 105, 103, 105, 110, 97, 108, 32, 116, 97, 99, 116, 105, 99, 44, 32, 105, 102, 32, 112, 114, 101, 115, 101, 110, 116, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 61 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut crate::leanh::LeanObject,7294395221027647453 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,5315589541704216288 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut crate::leanh::LeanObject,7294395221027647453 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,9533205042951121276 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag___closed__0_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [116, 97, 99, 116, 105, 99, 95, 116, 97, 103, 0],
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_tactic__tag___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2771816669859235474 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_tactic__tag___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__tag: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value: crate::leanh::LeanStringObject<96> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [65, 100, 100, 115, 32, 111, 110, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 116, 97, 103, 115, 32, 116, 111, 32, 97, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 84, 97, 103, 115, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 99, 97, 110, 111, 110, 105, 99, 97, 108, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 116, 97, 99, 116, 105, 99, 115, 46, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 69 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value) as *mut crate::leanh::LeanObject,((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value) as *mut crate::leanh::LeanObject,((( 39 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value:
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
    m_fun: l_Lean_Parser_many1_formatter___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut crate::leanh::LeanObject,2771816669859235474 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,6159138967226915931 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value:
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
    m_fun: l_Lean_Parser_many1_parenthesizer___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut crate::leanh::LeanObject,2771816669859235474 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,17214893638470362495 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name___closed__0_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 97, 99, 116, 105, 99, 95, 110, 97, 109, 101, 0],
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Parser_Attr_tactic__name___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
                as *mut crate::leanh::LeanObject,
            744976359190887801 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Parser_Attr_tactic__name___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Attr_tactic__name___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__name: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value: crate::leanh::LeanStringObject<392> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 392, m_capacity: 392, m_length: 391, m_data: [83, 101, 116, 115, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 46, 10, 10, 79, 114, 100, 105, 110, 97, 114, 105, 108, 121, 44, 32, 116, 97, 99, 116, 105, 99, 32, 110, 97, 109, 101, 115, 32, 97, 114, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 101, 116, 32, 116, 111, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 116, 111, 107, 101, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 112, 97, 114, 115, 101, 114, 46, 32, 73, 102, 32, 116, 104, 105, 115, 10, 112, 114, 111, 99, 101, 115, 115, 32, 102, 97, 105, 108, 115, 44, 32, 111, 114, 32, 105, 102, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 116, 111, 107, 101, 110, 115, 32, 40, 101, 46, 103, 46, 32, 96, 108, 101, 116, 32, 114, 101, 99, 96, 41, 44, 32, 116, 104, 101, 110, 32, 116, 104, 105, 115, 10, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 112, 114, 111, 118, 105, 100, 101, 32, 97, 32, 110, 97, 109, 101, 46, 10, 10, 84, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 32, 105, 115, 32, 117, 115, 101, 100, 32, 105, 110, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 97, 115, 32, 119, 101, 108, 108, 32, 97, 115, 32, 105, 110, 32, 99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 46, 32, 84, 104, 117, 115, 44, 32, 116, 104, 101, 32, 110, 97, 109, 101, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 10, 118, 97, 108, 105, 100, 32, 112, 114, 101, 102, 105, 120, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 115, 121, 110, 116, 97, 120, 46, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value:
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
    m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut crate::leanh::LeanObject,744976359190887801 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject,4560258218019812116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value:
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
    m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((1024 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4584992172905639687 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut crate::leanh::LeanObject,744976359190887801 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject,6627616489404433736 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2516_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2517_ = 2;
    v___x_2518_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2519_ = l_Lean_Parser_registerBuiltinParserAttribute(
        v___x_2515_,
        v___x_2516_,
        v___x_2517_,
        v___x_2518_,
    );
    if crate::leanh::lean_obj_tag(v___x_2519_) == 0 {
        let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2519_, 1);
        v___x_2520_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
        v___x_2521_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
        v___x_2522_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(
            v___x_2520_,
            v___x_2521_,
            v___x_2518_,
        );
        return v___x_2522_;
    } else {
        return v___x_2519_;
    }
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2____boxed(
    mut v_a_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
    return v_res_2524_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2553_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2554_ = 1;
    v___x_2555_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2556_ = l_Lean_Parser_registerBuiltinParserAttribute(
        v___x_2552_,
        v___x_2553_,
        v___x_2554_,
        v___x_2555_,
    );
    if crate::leanh::lean_obj_tag(v___x_2556_) == 0 {
        let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_2556_, 1);
        v___x_2557_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
        v___x_2558_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
        v___x_2559_ = l_Lean_Parser_registerBuiltinDynamicParserAttribute(
            v___x_2557_,
            v___x_2558_,
            v___x_2555_,
        );
        return v___x_2559_;
    } else {
        return v___x_2556_;
    }
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2____boxed(
    mut v_a_2560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2561_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
    return v_res_2561_;
}
pub unsafe fn l_Lean_Parser_priorityParser(
    mut v_rbp_2562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2563_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2564_ = l_Lean_Parser_categoryParser(v___x_2563_, v_rbp_2562_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Parser_attrParser(
    mut v_rbp_2565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2567_ = l_Lean_Parser_categoryParser(v___x_2566_, v_rbp_2565_);
    return v___x_2567_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter___redArg(
    mut v_a_2568_: *mut crate::leanh::LeanObject,
    mut v_a_2569_: *mut crate::leanh::LeanObject,
    mut v_a_2570_: *mut crate::leanh::LeanObject,
    mut v_a_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2573_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2574_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(
        v___x_2573_,
        v_a_2568_,
        v_a_2569_,
        v_a_2570_,
        v_a_2571_,
    );
    return v___x_2574_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter___redArg___boxed(
    mut v_a_2575_: *mut crate::leanh::LeanObject,
    mut v_a_2576_: *mut crate::leanh::LeanObject,
    mut v_a_2577_: *mut crate::leanh::LeanObject,
    mut v_a_2578_: *mut crate::leanh::LeanObject,
    mut v_a_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2580_ =
        l_Lean_Parser_priorityParser_formatter___redArg(v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
    crate::leanh::lean_dec(v_a_2578_);
    crate::leanh::lean_dec_ref(v_a_2577_);
    crate::leanh::lean_dec(v_a_2576_);
    crate::leanh::lean_dec_ref(v_a_2575_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter(
    mut v_rbp_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ =
        l_Lean_Parser_priorityParser_formatter___redArg(v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
    return v___x_2587_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter___boxed(
    mut v_rbp_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_a_2590_: *mut crate::leanh::LeanObject,
    mut v_a_2591_: *mut crate::leanh::LeanObject,
    mut v_a_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Lean_Parser_priorityParser_formatter(
        v_rbp_2588_,
        v_a_2589_,
        v_a_2590_,
        v_a_2591_,
        v_a_2592_,
    );
    crate::leanh::lean_dec(v_a_2592_);
    crate::leanh::lean_dec_ref(v_a_2591_);
    crate::leanh::lean_dec(v_a_2590_);
    crate::leanh::lean_dec_ref(v_a_2589_);
    crate::leanh::lean_dec(v_rbp_2588_);
    return v_res_2594_;
}
pub unsafe fn l_Lean_Parser_priorityParser_parenthesizer(
    mut v_rbp_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
    mut v_a_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2601_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2602_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(
        v___x_2601_,
        v_rbp_2595_,
        v_a_2596_,
        v_a_2597_,
        v_a_2598_,
        v_a_2599_,
    );
    return v___x_2602_;
}
pub unsafe fn l_Lean_Parser_priorityParser_parenthesizer___boxed(
    mut v_rbp_2603_: *mut crate::leanh::LeanObject,
    mut v_a_2604_: *mut crate::leanh::LeanObject,
    mut v_a_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Lean_Parser_priorityParser_parenthesizer(
        v_rbp_2603_,
        v_a_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
    );
    crate::leanh::lean_dec(v_a_2607_);
    crate::leanh::lean_dec_ref(v_a_2606_);
    crate::leanh::lean_dec(v_a_2605_);
    crate::leanh::lean_dec_ref(v_a_2604_);
    return v_res_2609_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter___redArg(
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2615_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2616_ = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter(
        v___x_2615_,
        v_a_2610_,
        v_a_2611_,
        v_a_2612_,
        v_a_2613_,
    );
    return v___x_2616_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter___redArg___boxed(
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2622_ =
        l_Lean_Parser_attrParser_formatter___redArg(v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
    crate::leanh::lean_dec(v_a_2620_);
    crate::leanh::lean_dec_ref(v_a_2619_);
    crate::leanh::lean_dec(v_a_2618_);
    crate::leanh::lean_dec_ref(v_a_2617_);
    return v_res_2622_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter(
    mut v_rbp_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ =
        l_Lean_Parser_attrParser_formatter___redArg(v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
    return v___x_2629_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter___boxed(
    mut v_rbp_2630_: *mut crate::leanh::LeanObject,
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_a_2632_: *mut crate::leanh::LeanObject,
    mut v_a_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2636_ =
        l_Lean_Parser_attrParser_formatter(v_rbp_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
    crate::leanh::lean_dec(v_a_2634_);
    crate::leanh::lean_dec_ref(v_a_2633_);
    crate::leanh::lean_dec(v_a_2632_);
    crate::leanh::lean_dec_ref(v_a_2631_);
    crate::leanh::lean_dec(v_rbp_2630_);
    return v_res_2636_;
}
pub unsafe fn l_Lean_Parser_attrParser_parenthesizer(
    mut v_rbp_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2643_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2644_ = l_Lean_PrettyPrinter_Parenthesizer_categoryParser_parenthesizer(
        v___x_2643_,
        v_rbp_2637_,
        v_a_2638_,
        v_a_2639_,
        v_a_2640_,
        v_a_2641_,
    );
    return v___x_2644_;
}
pub unsafe fn l_Lean_Parser_attrParser_parenthesizer___boxed(
    mut v_rbp_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
    mut v_a_2648_: *mut crate::leanh::LeanObject,
    mut v_a_2649_: *mut crate::leanh::LeanObject,
    mut v_a_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Parser_attrParser_parenthesizer(
        v_rbp_2645_,
        v_a_2646_,
        v_a_2647_,
        v_a_2648_,
        v_a_2649_,
    );
    crate::leanh::lean_dec(v_a_2649_);
    crate::leanh::lean_dec_ref(v_a_2648_);
    crate::leanh::lean_dec(v_a_2647_);
    crate::leanh::lean_dec_ref(v_a_2646_);
    return v_res_2651_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Lean_Parser_maxPrec;
    v___x_2653_ = l_Lean_Parser_checkPrec(v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2654_ = l_Lean_Parser_numLit;
    v___x_2655_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__0_once),
        _init_l_Lean_Parser_Priority_numPrio___closed__0,
    );
    v___x_2656_ = l_Lean_Parser_andthen(v___x_2655_, v___x_2654_);
    return v___x_2656_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio() -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__1_once),
        _init_l_Lean_Parser_Priority_numPrio___closed__1,
    );
    return v___x_2657_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2667_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2;
    v___x_2668_ = l_Lean_Parser_Priority_numPrio;
    v___x_2669_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2670_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2666_, v___x_2667_, v___x_2668_, v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___boxed(
    mut v_a_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
    return v_res_2672_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2699_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2;
    v___x_2700_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6;
    v___x_2701_ = l_Lean_addBuiltinDeclarationRanges(v___x_2699_, v___x_2700_);
    return v___x_2701_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___boxed(
    mut v_a_2702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
    return v_res_2703_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_formatter(
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_checkPrec_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2711_ = l_Lean_Parser_Priority_numPrio_formatter___closed__0;
    v___x_2712_ = l_Lean_PrettyPrinter_Formatter_andthen_formatter(
        v___x_2710_,
        v___x_2711_,
        v_a_2705_,
        v_a_2706_,
        v_a_2707_,
        v_a_2708_,
    );
    return v___x_2712_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_formatter___boxed(
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_a_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ =
        l_Lean_Parser_Priority_numPrio_formatter(v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
    crate::leanh::lean_dec(v_a_2716_);
    crate::leanh::lean_dec_ref(v_a_2715_);
    crate::leanh::lean_dec(v_a_2714_);
    crate::leanh::lean_dec_ref(v_a_2713_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(
    mut v___x_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ =
        l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_2719_, v___y_2721_);
    return v___x_2725_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(
    mut v___x_2726_: *mut crate::leanh::LeanObject,
    mut v___y_2727_: *mut crate::leanh::LeanObject,
    mut v___y_2728_: *mut crate::leanh::LeanObject,
    mut v___y_2729_: *mut crate::leanh::LeanObject,
    mut v___y_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(
        v___x_2726_,
        v___y_2727_,
        v___y_2728_,
        v___y_2729_,
        v___y_2730_,
    );
    crate::leanh::lean_dec(v___y_2730_);
    crate::leanh::lean_dec_ref(v___y_2729_);
    crate::leanh::lean_dec(v___y_2728_);
    crate::leanh::lean_dec_ref(v___y_2727_);
    return v_res_2732_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Parser_maxPrec;
    v___f_2734_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2734_, 0, v___x_2733_);
    return v___f_2734_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer(
    mut v_a_2736_: *mut crate::leanh::LeanObject,
    mut v_a_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2741_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0_once),
        _init_l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0,
    );
    v___x_2742_ = l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1;
    v___x_2743_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(
        v___f_2741_,
        v___x_2742_,
        v_a_2736_,
        v_a_2737_,
        v_a_2738_,
        v_a_2739_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer___boxed(
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
    mut v_a_2747_: *mut crate::leanh::LeanObject,
    mut v_a_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2749_ =
        l_Lean_Parser_Priority_numPrio_parenthesizer(v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
    crate::leanh::lean_dec(v_a_2747_);
    crate::leanh::lean_dec_ref(v_a_2746_);
    crate::leanh::lean_dec(v_a_2745_);
    crate::leanh::lean_dec_ref(v_a_2744_);
    return v_res_2749_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: u8 = 0;
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = 0;
    v___x_2757_ = 1;
    v___x_2758_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2759_ = l_Lean_Parser_Attr_simple___closed__0;
    v___x_2760_ = l_Lean_Parser_mkAntiquot(v___x_2759_, v___x_2758_, v___x_2757_, v___x_2756_);
    return v___x_2760_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2762_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2763_ = l_Lean_Parser_categoryParser(v___x_2762_, v___x_2761_);
    return v___x_2763_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2764_ = l_Lean_Parser_ident;
    v___x_2765_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3_once),
        _init_l_Lean_Parser_Attr_simple___closed__3,
    );
    v___x_2766_ = l_Lean_Parser_orelse(v___x_2765_, v___x_2764_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2767_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__4_once),
        _init_l_Lean_Parser_Attr_simple___closed__4,
    );
    v___x_2768_ = l_Lean_Parser_skip;
    v___x_2769_ = l_Lean_Parser_andthen(v___x_2768_, v___x_2767_);
    return v___x_2769_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2770_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__5_once),
        _init_l_Lean_Parser_Attr_simple___closed__5,
    );
    v___x_2771_ = l_Lean_Parser_optional(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__6_once),
        _init_l_Lean_Parser_Attr_simple___closed__6,
    );
    v___x_2773_ = l_Lean_Parser_ident;
    v___x_2774_ = l_Lean_Parser_andthen(v___x_2773_, v___x_2772_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__7_once),
        _init_l_Lean_Parser_Attr_simple___closed__7,
    );
    v___x_2776_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2777_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2778_ = l_Lean_Parser_leadingNode(v___x_2777_, v___x_2776_, v___x_2775_);
    return v___x_2778_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2779_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__8_once),
        _init_l_Lean_Parser_Attr_simple___closed__8,
    );
    v___x_2780_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__2_once),
        _init_l_Lean_Parser_Attr_simple___closed__2,
    );
    v___x_2781_ = l_Lean_Parser_withAntiquot(v___x_2780_, v___x_2779_);
    return v___x_2781_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__9_once),
        _init_l_Lean_Parser_Attr_simple___closed__9,
    );
    v___x_2783_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2784_ = l_Lean_Parser_withCache(v___x_2783_, v___x_2782_);
    return v___x_2784_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple() -> *mut crate::leanh::LeanObject {
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2785_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__10_once),
        _init_l_Lean_Parser_Attr_simple___closed__10,
    );
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2787_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2788_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2789_ = l_Lean_Parser_Attr_simple;
    v___x_2790_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2791_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2787_, v___x_2788_, v___x_2789_, v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1___boxed(
    mut v_a_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2793_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
    return v_res_2793_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2820_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2821_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6;
    v___x_2822_ = l_Lean_addBuiltinDeclarationRanges(v___x_2820_, v___x_2821_);
    return v___x_2822_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___boxed(
    mut v_a_2823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
    return v_res_2824_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter___lam__0(
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2826_);
    return v___x_2830_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_Parser_Attr_simple_formatter___lam__0(
        v___y_2831_,
        v___y_2832_,
        v___y_2833_,
        v___y_2834_,
    );
    crate::leanh::lean_dec(v___y_2834_);
    crate::leanh::lean_dec_ref(v___y_2833_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter(
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_Parser_Attr_simple_formatter___closed__1;
    v___x_2869_ = l_Lean_Parser_Attr_simple_formatter___closed__8;
    v___x_2870_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_2868_,
        v___x_2869_,
        v_a_2863_,
        v_a_2864_,
        v_a_2865_,
        v_a_2866_,
    );
    return v___x_2870_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter___boxed(
    mut v_a_2871_: *mut crate::leanh::LeanObject,
    mut v_a_2872_: *mut crate::leanh::LeanObject,
    mut v_a_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_a_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2876_ = l_Lean_Parser_Attr_simple_formatter(v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
    crate::leanh::lean_dec(v_a_2874_);
    crate::leanh::lean_dec_ref(v_a_2873_);
    crate::leanh::lean_dec(v_a_2872_);
    crate::leanh::lean_dec_ref(v_a_2871_);
    return v_res_2876_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_2886_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2887_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1;
    v___x_2888_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_simple_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2889_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2885_,
        v___x_2886_,
        v___x_2887_,
        v___x_2888_,
    );
    return v___x_2889_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___boxed(
    mut v_a_2890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
    return v_res_2891_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_parenthesizer(
    mut v_a_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_a_2920_: *mut crate::leanh::LeanObject,
    mut v_a_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2923_ = l_Lean_Parser_Attr_simple_parenthesizer___closed__0;
    v___x_2924_ = l_Lean_Parser_Attr_simple_parenthesizer___closed__8;
    v___x_2925_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_2923_,
        v___x_2924_,
        v_a_2918_,
        v_a_2919_,
        v_a_2920_,
        v_a_2921_,
    );
    return v___x_2925_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_parenthesizer___boxed(
    mut v_a_2926_: *mut crate::leanh::LeanObject,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2931_ =
        l_Lean_Parser_Attr_simple_parenthesizer(v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
    crate::leanh::lean_dec(v_a_2929_);
    crate::leanh::lean_dec_ref(v_a_2928_);
    crate::leanh::lean_dec(v_a_2927_);
    crate::leanh::lean_dec_ref(v_a_2926_);
    return v_res_2931_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2941_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2942_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1;
    v___x_2943_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_simple_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_2944_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2940_,
        v___x_2941_,
        v___x_2942_,
        v___x_2943_,
    );
    return v___x_2944_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___boxed(
    mut v_a_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2946_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
    return v_res_2946_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: u8 = 0;
    let mut v___x_2954_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = 0;
    v___x_2954_ = 1;
    v___x_2955_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2956_ = l_Lean_Parser_Attr_macro___closed__0;
    v___x_2957_ = l_Lean_Parser_mkAntiquot(v___x_2956_, v___x_2955_, v___x_2954_, v___x_2953_);
    return v___x_2957_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = l_Lean_Parser_Attr_macro___closed__3;
    v___x_2960_ = l_Lean_Parser_symbol(v___x_2959_);
    return v___x_2960_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_Parser_ident;
    v___x_2962_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__4_once),
        _init_l_Lean_Parser_Attr_macro___closed__4,
    );
    v___x_2963_ = l_Lean_Parser_andthen(v___x_2962_, v___x_2961_);
    return v___x_2963_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__5_once),
        _init_l_Lean_Parser_Attr_macro___closed__5,
    );
    v___x_2965_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_2966_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2967_ = l_Lean_Parser_leadingNode(v___x_2966_, v___x_2965_, v___x_2964_);
    return v___x_2967_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2968_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__6_once),
        _init_l_Lean_Parser_Attr_macro___closed__6,
    );
    v___x_2969_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__2_once),
        _init_l_Lean_Parser_Attr_macro___closed__2,
    );
    v___x_2970_ = l_Lean_Parser_withAntiquot(v___x_2969_, v___x_2968_);
    return v___x_2970_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2971_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__7_once),
        _init_l_Lean_Parser_Attr_macro___closed__7,
    );
    v___x_2972_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2973_ = l_Lean_Parser_withCache(v___x_2972_, v___x_2971_);
    return v___x_2973_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro() -> *mut crate::leanh::LeanObject {
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2974_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__8_once),
        _init_l_Lean_Parser_Attr_macro___closed__8,
    );
    return v___x_2974_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2977_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2978_ = l_Lean_Parser_Attr_macro;
    v___x_2979_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2980_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2976_, v___x_2977_, v___x_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1___boxed(
    mut v_a_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2982_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
    return v_res_2982_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3009_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3010_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6;
    v___x_3011_ = l_Lean_addBuiltinDeclarationRanges(v___x_3009_, v___x_3010_);
    return v___x_3011_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___boxed(
    mut v_a_3012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3013_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
    return v_res_3013_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_formatter(
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3035_ = l_Lean_Parser_Attr_macro_formatter___closed__0;
    v___x_3036_ = l_Lean_Parser_Attr_macro_formatter___closed__3;
    v___x_3037_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3035_,
        v___x_3036_,
        v_a_3030_,
        v_a_3031_,
        v_a_3032_,
        v_a_3033_,
    );
    return v___x_3037_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_formatter___boxed(
    mut v_a_3038_: *mut crate::leanh::LeanObject,
    mut v_a_3039_: *mut crate::leanh::LeanObject,
    mut v_a_3040_: *mut crate::leanh::LeanObject,
    mut v_a_3041_: *mut crate::leanh::LeanObject,
    mut v_a_3042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3043_ = l_Lean_Parser_Attr_macro_formatter(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
    crate::leanh::lean_dec(v_a_3041_);
    crate::leanh::lean_dec_ref(v_a_3040_);
    crate::leanh::lean_dec(v_a_3039_);
    crate::leanh::lean_dec_ref(v_a_3038_);
    return v_res_3043_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3052_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3053_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0;
    v___x_3054_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_macro_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3055_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3051_,
        v___x_3052_,
        v___x_3053_,
        v___x_3054_,
    );
    return v___x_3055_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___boxed(
    mut v_a_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3057_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
    return v_res_3057_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_parenthesizer(
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Lean_Parser_Attr_macro_parenthesizer___closed__0;
    v___x_3080_ = l_Lean_Parser_Attr_macro_parenthesizer___closed__3;
    v___x_3081_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3079_,
        v___x_3080_,
        v_a_3074_,
        v_a_3075_,
        v_a_3076_,
        v_a_3077_,
    );
    return v___x_3081_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_parenthesizer___boxed(
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3087_ =
        l_Lean_Parser_Attr_macro_parenthesizer(v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
    crate::leanh::lean_dec(v_a_3085_);
    crate::leanh::lean_dec_ref(v_a_3084_);
    crate::leanh::lean_dec(v_a_3083_);
    crate::leanh::lean_dec_ref(v_a_3082_);
    return v_res_3087_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3096_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3097_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0;
    v___x_3098_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_macro_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3099_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3095_,
        v___x_3096_,
        v___x_3097_,
        v___x_3098_,
    );
    return v___x_3099_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___boxed(
    mut v_a_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3101_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
    return v_res_3101_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3108_ = 0;
    v___x_3109_ = 1;
    v___x_3110_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3111_ = l_Lean_Parser_Attr_export___closed__0;
    v___x_3112_ = l_Lean_Parser_mkAntiquot(v___x_3111_, v___x_3110_, v___x_3109_, v___x_3108_);
    return v___x_3112_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Parser_Attr_export___closed__3;
    v___x_3115_ = l_Lean_Parser_symbol(v___x_3114_);
    return v___x_3115_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = l_Lean_Parser_ident;
    v___x_3117_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__4_once),
        _init_l_Lean_Parser_Attr_export___closed__4,
    );
    v___x_3118_ = l_Lean_Parser_andthen(v___x_3117_, v___x_3116_);
    return v___x_3118_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3119_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__5_once),
        _init_l_Lean_Parser_Attr_export___closed__5,
    );
    v___x_3120_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3121_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3122_ = l_Lean_Parser_leadingNode(v___x_3121_, v___x_3120_, v___x_3119_);
    return v___x_3122_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__6_once),
        _init_l_Lean_Parser_Attr_export___closed__6,
    );
    v___x_3124_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__2_once),
        _init_l_Lean_Parser_Attr_export___closed__2,
    );
    v___x_3125_ = l_Lean_Parser_withAntiquot(v___x_3124_, v___x_3123_);
    return v___x_3125_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3126_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__7_once),
        _init_l_Lean_Parser_Attr_export___closed__7,
    );
    v___x_3127_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3128_ = l_Lean_Parser_withCache(v___x_3127_, v___x_3126_);
    return v___x_3128_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export() -> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__8_once),
        _init_l_Lean_Parser_Attr_export___closed__8,
    );
    return v___x_3129_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3132_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3133_ = l_Lean_Parser_Attr_export;
    v___x_3134_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3135_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3131_, v___x_3132_, v___x_3133_, v___x_3134_);
    return v___x_3135_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1___boxed(
    mut v_a_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3137_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
    return v_res_3137_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3164_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3165_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6;
    v___x_3166_ = l_Lean_addBuiltinDeclarationRanges(v___x_3164_, v___x_3165_);
    return v___x_3166_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___boxed(
    mut v_a_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3168_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
    return v_res_3168_;
}
pub unsafe fn l_Lean_Parser_Attr_export_formatter(
    mut v_a_3185_: *mut crate::leanh::LeanObject,
    mut v_a_3186_: *mut crate::leanh::LeanObject,
    mut v_a_3187_: *mut crate::leanh::LeanObject,
    mut v_a_3188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = l_Lean_Parser_Attr_export_formatter___closed__0;
    v___x_3191_ = l_Lean_Parser_Attr_export_formatter___closed__3;
    v___x_3192_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3190_,
        v___x_3191_,
        v_a_3185_,
        v_a_3186_,
        v_a_3187_,
        v_a_3188_,
    );
    return v___x_3192_;
}
pub unsafe fn l_Lean_Parser_Attr_export_formatter___boxed(
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
    mut v_a_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_Parser_Attr_export_formatter(v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
    crate::leanh::lean_dec(v_a_3196_);
    crate::leanh::lean_dec_ref(v_a_3195_);
    crate::leanh::lean_dec(v_a_3194_);
    crate::leanh::lean_dec_ref(v_a_3193_);
    return v_res_3198_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3207_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3208_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0;
    v___x_3209_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_export_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3210_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3206_,
        v___x_3207_,
        v___x_3208_,
        v___x_3209_,
    );
    return v___x_3210_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___boxed(
    mut v_a_3211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3212_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
    return v_res_3212_;
}
pub unsafe fn l_Lean_Parser_Attr_export_parenthesizer(
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = l_Lean_Parser_Attr_export_parenthesizer___closed__0;
    v___x_3235_ = l_Lean_Parser_Attr_export_parenthesizer___closed__3;
    v___x_3236_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3234_,
        v___x_3235_,
        v_a_3229_,
        v_a_3230_,
        v_a_3231_,
        v_a_3232_,
    );
    return v___x_3236_;
}
pub unsafe fn l_Lean_Parser_Attr_export_parenthesizer___boxed(
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
    mut v_a_3240_: *mut crate::leanh::LeanObject,
    mut v_a_3241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3242_ =
        l_Lean_Parser_Attr_export_parenthesizer(v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
    crate::leanh::lean_dec(v_a_3240_);
    crate::leanh::lean_dec_ref(v_a_3239_);
    crate::leanh::lean_dec(v_a_3238_);
    crate::leanh::lean_dec_ref(v_a_3237_);
    return v_res_3242_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3251_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3252_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0;
    v___x_3253_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_export_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3254_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3250_,
        v___x_3251_,
        v___x_3252_,
        v___x_3253_,
    );
    return v___x_3254_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___boxed(
    mut v_a_3255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3256_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
    return v_res_3256_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = 0;
    v___x_3264_ = 1;
    v___x_3265_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3266_ = l_Lean_Parser_Attr_recursor___closed__0;
    v___x_3267_ = l_Lean_Parser_mkAntiquot(v___x_3266_, v___x_3265_, v___x_3264_, v___x_3263_);
    return v___x_3267_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3269_ = 0;
    v___x_3270_ = l_Lean_Parser_Attr_recursor___closed__3;
    v___x_3271_ = l_Lean_Parser_nonReservedSymbol(v___x_3270_, v___x_3269_);
    return v___x_3271_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Lean_Parser_numLit;
    v___x_3273_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__4_once),
        _init_l_Lean_Parser_Attr_recursor___closed__4,
    );
    v___x_3274_ = l_Lean_Parser_andthen(v___x_3273_, v___x_3272_);
    return v___x_3274_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__5_once),
        _init_l_Lean_Parser_Attr_recursor___closed__5,
    );
    v___x_3276_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3277_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3278_ = l_Lean_Parser_leadingNode(v___x_3277_, v___x_3276_, v___x_3275_);
    return v___x_3278_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__6_once),
        _init_l_Lean_Parser_Attr_recursor___closed__6,
    );
    v___x_3280_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__2_once),
        _init_l_Lean_Parser_Attr_recursor___closed__2,
    );
    v___x_3281_ = l_Lean_Parser_withAntiquot(v___x_3280_, v___x_3279_);
    return v___x_3281_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__7_once),
        _init_l_Lean_Parser_Attr_recursor___closed__7,
    );
    v___x_3283_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3284_ = l_Lean_Parser_withCache(v___x_3283_, v___x_3282_);
    return v___x_3284_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor() -> *mut crate::leanh::LeanObject {
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__8_once),
        _init_l_Lean_Parser_Attr_recursor___closed__8,
    );
    return v___x_3285_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3287_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3288_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3289_ = l_Lean_Parser_Attr_recursor;
    v___x_3290_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3291_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3287_, v___x_3288_, v___x_3289_, v___x_3290_);
    return v___x_3291_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1___boxed(
    mut v_a_3292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3293_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
    return v_res_3293_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3321_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6;
    v___x_3322_ = l_Lean_addBuiltinDeclarationRanges(v___x_3320_, v___x_3321_);
    return v___x_3322_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___boxed(
    mut v_a_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3324_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
    return v_res_3324_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_formatter(
    mut v_a_3343_: *mut crate::leanh::LeanObject,
    mut v_a_3344_: *mut crate::leanh::LeanObject,
    mut v_a_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l_Lean_Parser_Attr_recursor_formatter___closed__0;
    v___x_3349_ = l_Lean_Parser_Attr_recursor_formatter___closed__3;
    v___x_3350_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3348_,
        v___x_3349_,
        v_a_3343_,
        v_a_3344_,
        v_a_3345_,
        v_a_3346_,
    );
    return v___x_3350_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_formatter___boxed(
    mut v_a_3351_: *mut crate::leanh::LeanObject,
    mut v_a_3352_: *mut crate::leanh::LeanObject,
    mut v_a_3353_: *mut crate::leanh::LeanObject,
    mut v_a_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3356_ = l_Lean_Parser_Attr_recursor_formatter(v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
    crate::leanh::lean_dec(v_a_3354_);
    crate::leanh::lean_dec_ref(v_a_3353_);
    crate::leanh::lean_dec(v_a_3352_);
    crate::leanh::lean_dec_ref(v_a_3351_);
    return v_res_3356_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3364_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3365_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3366_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0;
    v___x_3367_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_recursor_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3368_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3364_,
        v___x_3365_,
        v___x_3366_,
        v___x_3367_,
    );
    return v___x_3368_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___boxed(
    mut v_a_3369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3370_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
    return v_res_3370_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_parenthesizer(
    mut v_a_3389_: *mut crate::leanh::LeanObject,
    mut v_a_3390_: *mut crate::leanh::LeanObject,
    mut v_a_3391_: *mut crate::leanh::LeanObject,
    mut v_a_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Lean_Parser_Attr_recursor_parenthesizer___closed__0;
    v___x_3395_ = l_Lean_Parser_Attr_recursor_parenthesizer___closed__3;
    v___x_3396_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3394_,
        v___x_3395_,
        v_a_3389_,
        v_a_3390_,
        v_a_3391_,
        v_a_3392_,
    );
    return v___x_3396_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_parenthesizer___boxed(
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
    mut v_a_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3402_ =
        l_Lean_Parser_Attr_recursor_parenthesizer(v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
    crate::leanh::lean_dec(v_a_3400_);
    crate::leanh::lean_dec_ref(v_a_3399_);
    crate::leanh::lean_dec(v_a_3398_);
    crate::leanh::lean_dec_ref(v_a_3397_);
    return v_res_3402_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3411_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3412_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0;
    v___x_3413_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_recursor_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3410_,
        v___x_3411_,
        v___x_3412_,
        v___x_3413_,
    );
    return v___x_3414_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___boxed(
    mut v_a_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
    return v_res_3416_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3423_ = 0;
    v___x_3424_ = 1;
    v___x_3425_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3426_ = l_Lean_Parser_Attr_class___closed__0;
    v___x_3427_ = l_Lean_Parser_mkAntiquot(v___x_3426_, v___x_3425_, v___x_3424_, v___x_3423_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_Parser_Attr_class___closed__0;
    v___x_3429_ = l_Lean_Parser_symbol(v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__3_once),
        _init_l_Lean_Parser_Attr_class___closed__3,
    );
    v___x_3431_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3432_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3433_ = l_Lean_Parser_leadingNode(v___x_3432_, v___x_3431_, v___x_3430_);
    return v___x_3433_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__4_once),
        _init_l_Lean_Parser_Attr_class___closed__4,
    );
    v___x_3435_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__2_once),
        _init_l_Lean_Parser_Attr_class___closed__2,
    );
    v___x_3436_ = l_Lean_Parser_withAntiquot(v___x_3435_, v___x_3434_);
    return v___x_3436_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3437_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__5_once),
        _init_l_Lean_Parser_Attr_class___closed__5,
    );
    v___x_3438_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3439_ = l_Lean_Parser_withCache(v___x_3438_, v___x_3437_);
    return v___x_3439_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class() -> *mut crate::leanh::LeanObject {
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__6_once),
        _init_l_Lean_Parser_Attr_class___closed__6,
    );
    return v___x_3440_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3442_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3443_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3444_ = l_Lean_Parser_Attr_class;
    v___x_3445_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3446_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3442_, v___x_3443_, v___x_3444_, v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1___boxed(
    mut v_a_3447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
    return v_res_3448_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3476_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6;
    v___x_3477_ = l_Lean_addBuiltinDeclarationRanges(v___x_3475_, v___x_3476_);
    return v___x_3477_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___boxed(
    mut v_a_3478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3479_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
    return v_res_3479_;
}
pub unsafe fn l_Lean_Parser_Attr_class_formatter(
    mut v_a_3493_: *mut crate::leanh::LeanObject,
    mut v_a_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3498_ = l_Lean_Parser_Attr_class_formatter___closed__0;
    v___x_3499_ = l_Lean_Parser_Attr_class_formatter___closed__2;
    v___x_3500_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3498_,
        v___x_3499_,
        v_a_3493_,
        v_a_3494_,
        v_a_3495_,
        v_a_3496_,
    );
    return v___x_3500_;
}
pub unsafe fn l_Lean_Parser_Attr_class_formatter___boxed(
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Parser_Attr_class_formatter(v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
    crate::leanh::lean_dec(v_a_3504_);
    crate::leanh::lean_dec_ref(v_a_3503_);
    crate::leanh::lean_dec(v_a_3502_);
    crate::leanh::lean_dec_ref(v_a_3501_);
    return v_res_3506_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3515_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3516_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0;
    v___x_3517_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_class_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3518_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3514_,
        v___x_3515_,
        v___x_3516_,
        v___x_3517_,
    );
    return v___x_3518_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___boxed(
    mut v_a_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
    return v_res_3520_;
}
pub unsafe fn l_Lean_Parser_Attr_class_parenthesizer(
    mut v_a_3534_: *mut crate::leanh::LeanObject,
    mut v_a_3535_: *mut crate::leanh::LeanObject,
    mut v_a_3536_: *mut crate::leanh::LeanObject,
    mut v_a_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3539_ = l_Lean_Parser_Attr_class_parenthesizer___closed__0;
    v___x_3540_ = l_Lean_Parser_Attr_class_parenthesizer___closed__2;
    v___x_3541_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3539_,
        v___x_3540_,
        v_a_3534_,
        v_a_3535_,
        v_a_3536_,
        v_a_3537_,
    );
    return v___x_3541_;
}
pub unsafe fn l_Lean_Parser_Attr_class_parenthesizer___boxed(
    mut v_a_3542_: *mut crate::leanh::LeanObject,
    mut v_a_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ =
        l_Lean_Parser_Attr_class_parenthesizer(v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
    crate::leanh::lean_dec(v_a_3545_);
    crate::leanh::lean_dec_ref(v_a_3544_);
    crate::leanh::lean_dec(v_a_3543_);
    crate::leanh::lean_dec_ref(v_a_3542_);
    return v_res_3547_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3556_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3557_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0;
    v___x_3558_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_class_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3559_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3555_,
        v___x_3556_,
        v___x_3557_,
        v___x_3558_,
    );
    return v___x_3559_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___boxed(
    mut v_a_3560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
    return v_res_3561_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = 0;
    v___x_3569_ = 1;
    v___x_3570_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3571_ = l_Lean_Parser_Attr_instance___closed__0;
    v___x_3572_ = l_Lean_Parser_mkAntiquot(v___x_3571_, v___x_3570_, v___x_3569_, v___x_3568_);
    return v___x_3572_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_Parser_Attr_instance___closed__0;
    v___x_3574_ = l_Lean_Parser_symbol(v___x_3573_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3_once),
        _init_l_Lean_Parser_Attr_simple___closed__3,
    );
    v___x_3576_ = l_Lean_Parser_skip;
    v___x_3577_ = l_Lean_Parser_andthen(v___x_3576_, v___x_3575_);
    return v___x_3577_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__4_once),
        _init_l_Lean_Parser_Attr_instance___closed__4,
    );
    v___x_3579_ = l_Lean_Parser_optional(v___x_3578_);
    return v___x_3579_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5_once),
        _init_l_Lean_Parser_Attr_instance___closed__5,
    );
    v___x_3581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__3_once),
        _init_l_Lean_Parser_Attr_instance___closed__3,
    );
    v___x_3582_ = l_Lean_Parser_andthen(v___x_3581_, v___x_3580_);
    return v___x_3582_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__6_once),
        _init_l_Lean_Parser_Attr_instance___closed__6,
    );
    v___x_3584_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3585_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3586_ = l_Lean_Parser_leadingNode(v___x_3585_, v___x_3584_, v___x_3583_);
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__7_once),
        _init_l_Lean_Parser_Attr_instance___closed__7,
    );
    v___x_3588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__2_once),
        _init_l_Lean_Parser_Attr_instance___closed__2,
    );
    v___x_3589_ = l_Lean_Parser_withAntiquot(v___x_3588_, v___x_3587_);
    return v___x_3589_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3590_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__8_once),
        _init_l_Lean_Parser_Attr_instance___closed__8,
    );
    v___x_3591_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3592_ = l_Lean_Parser_withCache(v___x_3591_, v___x_3590_);
    return v___x_3592_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance() -> *mut crate::leanh::LeanObject {
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__9_once),
        _init_l_Lean_Parser_Attr_instance___closed__9,
    );
    return v___x_3593_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3596_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3597_ = l_Lean_Parser_Attr_instance;
    v___x_3598_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3599_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3595_, v___x_3596_, v___x_3597_, v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1___boxed(
    mut v_a_3600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3601_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
    return v_res_3601_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3628_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3629_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6;
    v___x_3630_ = l_Lean_addBuiltinDeclarationRanges(v___x_3628_, v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___boxed(
    mut v_a_3631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3632_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
    return v_res_3632_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_formatter(
    mut v_a_3654_: *mut crate::leanh::LeanObject,
    mut v_a_3655_: *mut crate::leanh::LeanObject,
    mut v_a_3656_: *mut crate::leanh::LeanObject,
    mut v_a_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = l_Lean_Parser_Attr_instance_formatter___closed__0;
    v___x_3660_ = l_Lean_Parser_Attr_instance_formatter___closed__5;
    v___x_3661_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3659_,
        v___x_3660_,
        v_a_3654_,
        v_a_3655_,
        v_a_3656_,
        v_a_3657_,
    );
    return v___x_3661_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_formatter___boxed(
    mut v_a_3662_: *mut crate::leanh::LeanObject,
    mut v_a_3663_: *mut crate::leanh::LeanObject,
    mut v_a_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
    mut v_a_3666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lean_Parser_Attr_instance_formatter(v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
    crate::leanh::lean_dec(v_a_3665_);
    crate::leanh::lean_dec_ref(v_a_3664_);
    crate::leanh::lean_dec(v_a_3663_);
    crate::leanh::lean_dec_ref(v_a_3662_);
    return v_res_3667_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3676_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3677_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0;
    v___x_3678_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_instance_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3679_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3675_,
        v___x_3676_,
        v___x_3677_,
        v___x_3678_,
    );
    return v___x_3679_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___boxed(
    mut v_a_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
    return v_res_3681_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_parenthesizer(
    mut v_a_3703_: *mut crate::leanh::LeanObject,
    mut v_a_3704_: *mut crate::leanh::LeanObject,
    mut v_a_3705_: *mut crate::leanh::LeanObject,
    mut v_a_3706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3708_ = l_Lean_Parser_Attr_instance_parenthesizer___closed__0;
    v___x_3709_ = l_Lean_Parser_Attr_instance_parenthesizer___closed__5;
    v___x_3710_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3708_,
        v___x_3709_,
        v_a_3703_,
        v_a_3704_,
        v_a_3705_,
        v_a_3706_,
    );
    return v___x_3710_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_parenthesizer___boxed(
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3716_ =
        l_Lean_Parser_Attr_instance_parenthesizer(v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
    crate::leanh::lean_dec(v_a_3714_);
    crate::leanh::lean_dec_ref(v_a_3713_);
    crate::leanh::lean_dec(v_a_3712_);
    crate::leanh::lean_dec_ref(v_a_3711_);
    return v_res_3716_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3725_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3726_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0;
    v___x_3727_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_instance_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3728_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3724_,
        v___x_3725_,
        v___x_3726_,
        v___x_3727_,
    );
    return v___x_3728_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___boxed(
    mut v_a_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3730_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
    return v_res_3730_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3737_ = 0;
    v___x_3738_ = 1;
    v___x_3739_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3740_ = l_Lean_Parser_Attr_default__instance___closed__0;
    v___x_3741_ = l_Lean_Parser_mkAntiquot(v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_);
    return v___x_3741_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3742_ = 0;
    v___x_3743_ = l_Lean_Parser_Attr_default__instance___closed__0;
    v___x_3744_ = l_Lean_Parser_nonReservedSymbol(v___x_3743_, v___x_3742_);
    return v___x_3744_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5_once),
        _init_l_Lean_Parser_Attr_instance___closed__5,
    );
    v___x_3746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__3_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__3,
    );
    v___x_3747_ = l_Lean_Parser_andthen(v___x_3746_, v___x_3745_);
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__4_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__4,
    );
    v___x_3749_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3750_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3751_ = l_Lean_Parser_leadingNode(v___x_3750_, v___x_3749_, v___x_3748_);
    return v___x_3751_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__5_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__5,
    );
    v___x_3753_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__2_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__2,
    );
    v___x_3754_ = l_Lean_Parser_withAntiquot(v___x_3753_, v___x_3752_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__6_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__6,
    );
    v___x_3756_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3757_ = l_Lean_Parser_withCache(v___x_3756_, v___x_3755_);
    return v___x_3757_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance() -> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__7_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__7,
    );
    return v___x_3758_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3760_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3761_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3762_ = l_Lean_Parser_Attr_default__instance;
    v___x_3763_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3764_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3760_, v___x_3761_, v___x_3762_, v___x_3763_);
    return v___x_3764_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1___boxed(
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
    return v_res_3766_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3793_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3794_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6;
    v___x_3795_ = l_Lean_addBuiltinDeclarationRanges(v___x_3793_, v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___boxed(
    mut v_a_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3797_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
    return v_res_3797_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_formatter(
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3821_ = l_Lean_Parser_Attr_default__instance_formatter___closed__0;
    v___x_3822_ = l_Lean_Parser_Attr_default__instance_formatter___closed__3;
    v___x_3823_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3821_,
        v___x_3822_,
        v_a_3816_,
        v_a_3817_,
        v_a_3818_,
        v_a_3819_,
    );
    return v___x_3823_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_formatter___boxed(
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
    mut v_a_3827_: *mut crate::leanh::LeanObject,
    mut v_a_3828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3829_ =
        l_Lean_Parser_Attr_default__instance_formatter(v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
    crate::leanh::lean_dec(v_a_3827_);
    crate::leanh::lean_dec_ref(v_a_3826_);
    crate::leanh::lean_dec(v_a_3825_);
    crate::leanh::lean_dec_ref(v_a_3824_);
    return v_res_3829_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3837_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3838_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3839_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0;
    v___x_3840_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_default__instance_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3841_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3837_,
        v___x_3838_,
        v___x_3839_,
        v___x_3840_,
    );
    return v___x_3841_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___boxed(
    mut v_a_3842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3843_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
    return v_res_3843_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_parenthesizer(
    mut v_a_3862_: *mut crate::leanh::LeanObject,
    mut v_a_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_a_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0;
    v___x_3868_ = l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3;
    v___x_3869_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_3867_,
        v___x_3868_,
        v_a_3862_,
        v_a_3863_,
        v_a_3864_,
        v_a_3865_,
    );
    return v___x_3869_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_parenthesizer___boxed(
    mut v_a_3870_: *mut crate::leanh::LeanObject,
    mut v_a_3871_: *mut crate::leanh::LeanObject,
    mut v_a_3872_: *mut crate::leanh::LeanObject,
    mut v_a_3873_: *mut crate::leanh::LeanObject,
    mut v_a_3874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_Parser_Attr_default__instance_parenthesizer(
        v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_,
    );
    crate::leanh::lean_dec(v_a_3873_);
    crate::leanh::lean_dec_ref(v_a_3872_);
    crate::leanh::lean_dec(v_a_3871_);
    crate::leanh::lean_dec_ref(v_a_3870_);
    return v_res_3875_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3884_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3885_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0;
    v___x_3886_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_default__instance_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_3887_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3883_,
        v___x_3884_,
        v___x_3885_,
        v___x_3886_,
    );
    return v___x_3887_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___boxed(
    mut v_a_3888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3889_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
    return v_res_3889_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = 0;
    v___x_3897_ = 1;
    v___x_3898_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3899_ = l_Lean_Parser_Attr_specialize___closed__0;
    v___x_3900_ = l_Lean_Parser_mkAntiquot(v___x_3899_, v___x_3898_, v___x_3897_, v___x_3896_);
    return v___x_3900_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3901_ = 0;
    v___x_3902_ = l_Lean_Parser_Attr_specialize___closed__0;
    v___x_3903_ = l_Lean_Parser_nonReservedSymbol(v___x_3902_, v___x_3901_);
    return v___x_3903_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = l_Lean_Parser_numLit;
    v___x_3905_ = l_Lean_Parser_ident;
    v___x_3906_ = l_Lean_Parser_orelse(v___x_3905_, v___x_3904_);
    return v___x_3906_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3907_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__4_once),
        _init_l_Lean_Parser_Attr_specialize___closed__4,
    );
    v___x_3908_ = l_Lean_Parser_skip;
    v___x_3909_ = l_Lean_Parser_andthen(v___x_3908_, v___x_3907_);
    return v___x_3909_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3910_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__5_once),
        _init_l_Lean_Parser_Attr_specialize___closed__5,
    );
    v___x_3911_ = l_Lean_Parser_many(v___x_3910_);
    return v___x_3911_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__6_once),
        _init_l_Lean_Parser_Attr_specialize___closed__6,
    );
    v___x_3913_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__3_once),
        _init_l_Lean_Parser_Attr_specialize___closed__3,
    );
    v___x_3914_ = l_Lean_Parser_andthen(v___x_3913_, v___x_3912_);
    return v___x_3914_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__7_once),
        _init_l_Lean_Parser_Attr_specialize___closed__7,
    );
    v___x_3916_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_3917_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3918_ = l_Lean_Parser_leadingNode(v___x_3917_, v___x_3916_, v___x_3915_);
    return v___x_3918_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__8_once),
        _init_l_Lean_Parser_Attr_specialize___closed__8,
    );
    v___x_3920_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__2_once),
        _init_l_Lean_Parser_Attr_specialize___closed__2,
    );
    v___x_3921_ = l_Lean_Parser_withAntiquot(v___x_3920_, v___x_3919_);
    return v___x_3921_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3922_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__9_once),
        _init_l_Lean_Parser_Attr_specialize___closed__9,
    );
    v___x_3923_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3924_ = l_Lean_Parser_withCache(v___x_3923_, v___x_3922_);
    return v___x_3924_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize() -> *mut crate::leanh::LeanObject {
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3925_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__10_once),
        _init_l_Lean_Parser_Attr_specialize___closed__10,
    );
    return v___x_3925_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3927_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3928_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3929_ = l_Lean_Parser_Attr_specialize;
    v___x_3930_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3931_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3927_, v___x_3928_, v___x_3929_, v___x_3930_);
    return v___x_3931_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1___boxed(
    mut v_a_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3933_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
    return v_res_3933_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3961_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6;
    v___x_3962_ = l_Lean_addBuiltinDeclarationRanges(v___x_3960_, v___x_3961_);
    return v___x_3962_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___boxed(
    mut v_a_3963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
    return v_res_3964_;
}
pub unsafe fn l_Lean_Parser_Attr_specialize_formatter(
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
    mut v_a_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = l_Lean_Parser_Attr_specialize_formatter___closed__0;
    v___x_3997_ = l_Lean_Parser_Attr_specialize_formatter___closed__6;
    v___x_3998_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_3996_,
        v___x_3997_,
        v_a_3991_,
        v_a_3992_,
        v_a_3993_,
        v_a_3994_,
    );
    return v___x_3998_;
}
pub unsafe fn l_Lean_Parser_Attr_specialize_formatter___boxed(
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4004_ =
        l_Lean_Parser_Attr_specialize_formatter(v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
    crate::leanh::lean_dec(v_a_4002_);
    crate::leanh::lean_dec_ref(v_a_4001_);
    crate::leanh::lean_dec(v_a_4000_);
    crate::leanh::lean_dec_ref(v_a_3999_);
    return v_res_4004_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4013_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_4014_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0;
    v___x_4015_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_specialize_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4016_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4012_,
        v___x_4013_,
        v___x_4014_,
        v___x_4015_,
    );
    return v___x_4016_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___boxed(
    mut v_a_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
    return v_res_4018_;
}
pub unsafe fn l_Lean_Parser_Attr_specialize_parenthesizer(
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_a_4046_: *mut crate::leanh::LeanObject,
    mut v_a_4047_: *mut crate::leanh::LeanObject,
    mut v_a_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l_Lean_Parser_Attr_specialize_parenthesizer___closed__0;
    v___x_4051_ = l_Lean_Parser_Attr_specialize_parenthesizer___closed__6;
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
pub unsafe fn l_Lean_Parser_Attr_specialize_parenthesizer___boxed(
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4058_ =
        l_Lean_Parser_Attr_specialize_parenthesizer(v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
    crate::leanh::lean_dec(v_a_4056_);
    crate::leanh::lean_dec_ref(v_a_4055_);
    crate::leanh::lean_dec(v_a_4054_);
    crate::leanh::lean_dec_ref(v_a_4053_);
    return v_res_4058_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4067_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_4068_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0;
    v___x_4069_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_specialize_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4070_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4066_,
        v___x_4067_,
        v___x_4068_,
        v___x_4069_,
    );
    return v___x_4070_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___boxed(
    mut v_a_4071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4072_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
    return v_res_4072_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4079_ = 0;
    v___x_4080_ = 1;
    v___x_4081_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4082_ = l_Lean_Parser_Attr_externEntry___closed__0;
    v___x_4083_ = l_Lean_Parser_mkAntiquot(v___x_4082_, v___x_4081_, v___x_4080_, v___x_4079_);
    return v___x_4083_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_Lean_Parser_skip;
    v___x_4085_ = l_Lean_Parser_ident;
    v___x_4086_ = l_Lean_Parser_andthen(v___x_4085_, v___x_4084_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4087_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__3_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__3,
    );
    v___x_4088_ = l_Lean_Parser_optional(v___x_4087_);
    return v___x_4088_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = 0;
    v___x_4091_ = l_Lean_Parser_Attr_externEntry___closed__5;
    v___x_4092_ = l_Lean_Parser_nonReservedSymbol(v___x_4091_, v___x_4090_);
    return v___x_4092_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4093_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__6_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__6,
    );
    v___x_4094_ = l_Lean_Parser_optional(v___x_4093_);
    return v___x_4094_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_Parser_strLit;
    v___x_4096_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__7_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__7,
    );
    v___x_4097_ = l_Lean_Parser_andthen(v___x_4096_, v___x_4095_);
    return v___x_4097_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__8_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__8,
    );
    v___x_4099_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__4_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__4,
    );
    v___x_4100_ = l_Lean_Parser_andthen(v___x_4099_, v___x_4098_);
    return v___x_4100_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__9_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__9,
    );
    v___x_4102_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4103_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4104_ = l_Lean_Parser_leadingNode(v___x_4103_, v___x_4102_, v___x_4101_);
    return v___x_4104_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__10_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__10,
    );
    v___x_4106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__2_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__2,
    );
    v___x_4107_ = l_Lean_Parser_withAntiquot(v___x_4106_, v___x_4105_);
    return v___x_4107_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4108_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__11_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__11,
    );
    v___x_4109_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4110_ = l_Lean_Parser_withCache(v___x_4109_, v___x_4108_);
    return v___x_4110_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry() -> *mut crate::leanh::LeanObject {
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4111_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__12_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__12,
    );
    return v___x_4111_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4118_ = 0;
    v___x_4119_ = 1;
    v___x_4120_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4121_ = l_Lean_Parser_Attr_extern___closed__0;
    v___x_4122_ = l_Lean_Parser_mkAntiquot(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_);
    return v___x_4122_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4123_ = 0;
    v___x_4124_ = l_Lean_Parser_Attr_extern___closed__0;
    v___x_4125_ = l_Lean_Parser_nonReservedSymbol(v___x_4124_, v___x_4123_);
    return v___x_4125_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4126_ = l_Lean_Parser_Attr_externEntry;
    v___x_4127_ = l_Lean_Parser_skip;
    v___x_4128_ = l_Lean_Parser_andthen(v___x_4127_, v___x_4126_);
    return v___x_4128_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__4_once),
        _init_l_Lean_Parser_Attr_extern___closed__4,
    );
    v___x_4130_ = l_Lean_Parser_many(v___x_4129_);
    return v___x_4130_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__5_once),
        _init_l_Lean_Parser_Attr_extern___closed__5,
    );
    v___x_4132_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__3_once),
        _init_l_Lean_Parser_Attr_extern___closed__3,
    );
    v___x_4133_ = l_Lean_Parser_andthen(v___x_4132_, v___x_4131_);
    return v___x_4133_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__6_once),
        _init_l_Lean_Parser_Attr_extern___closed__6,
    );
    v___x_4135_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4136_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4137_ = l_Lean_Parser_leadingNode(v___x_4136_, v___x_4135_, v___x_4134_);
    return v___x_4137_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__7_once),
        _init_l_Lean_Parser_Attr_extern___closed__7,
    );
    v___x_4139_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__2_once),
        _init_l_Lean_Parser_Attr_extern___closed__2,
    );
    v___x_4140_ = l_Lean_Parser_withAntiquot(v___x_4139_, v___x_4138_);
    return v___x_4140_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4141_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__8_once),
        _init_l_Lean_Parser_Attr_extern___closed__8,
    );
    v___x_4142_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4143_ = l_Lean_Parser_withCache(v___x_4142_, v___x_4141_);
    return v___x_4143_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern() -> *mut crate::leanh::LeanObject {
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4144_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__9_once),
        _init_l_Lean_Parser_Attr_extern___closed__9,
    );
    return v___x_4144_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4147_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4148_ = l_Lean_Parser_Attr_extern;
    v___x_4149_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4150_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4146_, v___x_4147_, v___x_4148_, v___x_4149_);
    return v___x_4150_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1___boxed(
    mut v_a_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
    return v_res_4152_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4179_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4180_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6;
    v___x_4181_ = l_Lean_addBuiltinDeclarationRanges(v___x_4179_, v___x_4180_);
    return v___x_4181_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___boxed(
    mut v_a_4182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4183_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
    return v_res_4183_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_formatter(
    mut v_a_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4218_ = l_Lean_Parser_Attr_externEntry_formatter___closed__0;
    v___x_4219_ = l_Lean_Parser_Attr_externEntry_formatter___closed__8;
    v___x_4220_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4218_,
        v___x_4219_,
        v_a_4213_,
        v_a_4214_,
        v_a_4215_,
        v_a_4216_,
    );
    return v___x_4220_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_formatter___boxed(
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
    mut v_a_4223_: *mut crate::leanh::LeanObject,
    mut v_a_4224_: *mut crate::leanh::LeanObject,
    mut v_a_4225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4226_ =
        l_Lean_Parser_Attr_externEntry_formatter(v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_);
    crate::leanh::lean_dec(v_a_4224_);
    crate::leanh::lean_dec_ref(v_a_4223_);
    crate::leanh::lean_dec(v_a_4222_);
    crate::leanh::lean_dec_ref(v_a_4221_);
    return v_res_4226_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4235_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4236_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0;
    v___x_4237_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4234_,
        v___x_4235_,
        v___x_4236_,
        v___x_4237_,
    );
    return v___x_4238_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___boxed(
    mut v_a_4239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4240_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
    return v_res_4240_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4252_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___f_4253_ = l_Lean_Parser_Attr_simple_formatter___closed__0;
    v___x_4254_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4254_, 0, v___f_4253_);
    crate::leanh::lean_closure_set(v___x_4254_, 1, v___x_4252_);
    return v___x_4254_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__2_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__2,
    );
    v___x_4256_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4256_, 0, v___x_4255_);
    return v___x_4256_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__3_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__3,
    );
    v___x_4258_ = l_Lean_Parser_Attr_extern_formatter___closed__1;
    v___x_4259_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4259_, 0, v___x_4258_);
    crate::leanh::lean_closure_set(v___x_4259_, 1, v___x_4257_);
    return v___x_4259_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4260_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__4_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__4,
    );
    v___x_4261_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4262_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4263_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4263_, 0, v___x_4262_);
    crate::leanh::lean_closure_set(v___x_4263_, 1, v___x_4261_);
    crate::leanh::lean_closure_set(v___x_4263_, 2, v___x_4260_);
    return v___x_4263_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_formatter(
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = l_Lean_Parser_Attr_extern_formatter___closed__0;
    v___x_4270_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__5_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__5,
    );
    v___x_4271_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4269_,
        v___x_4270_,
        v_a_4264_,
        v_a_4265_,
        v_a_4266_,
        v_a_4267_,
    );
    return v___x_4271_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_formatter___boxed(
    mut v_a_4272_: *mut crate::leanh::LeanObject,
    mut v_a_4273_: *mut crate::leanh::LeanObject,
    mut v_a_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_Parser_Attr_extern_formatter(v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
    crate::leanh::lean_dec(v_a_4275_);
    crate::leanh::lean_dec_ref(v_a_4274_);
    crate::leanh::lean_dec(v_a_4273_);
    crate::leanh::lean_dec_ref(v_a_4272_);
    return v_res_4277_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4286_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4287_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0;
    v___x_4288_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_extern_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4289_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4285_,
        v___x_4286_,
        v___x_4287_,
        v___x_4288_,
    );
    return v___x_4289_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___boxed(
    mut v_a_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4291_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
    return v_res_4291_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_parenthesizer(
    mut v_a_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0;
    v___x_4327_ = l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8;
    v___x_4328_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4326_,
        v___x_4327_,
        v_a_4321_,
        v_a_4322_,
        v_a_4323_,
        v_a_4324_,
    );
    return v___x_4328_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_parenthesizer___boxed(
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_a_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
    mut v_a_4333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4334_ =
        l_Lean_Parser_Attr_externEntry_parenthesizer(v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_);
    crate::leanh::lean_dec(v_a_4332_);
    crate::leanh::lean_dec_ref(v_a_4331_);
    crate::leanh::lean_dec(v_a_4330_);
    crate::leanh::lean_dec_ref(v_a_4329_);
    return v_res_4334_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4343_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4344_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0;
    v___x_4345_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4346_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4342_,
        v___x_4343_,
        v___x_4344_,
        v___x_4345_,
    );
    return v___x_4346_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___boxed(
    mut v_a_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4348_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
    return v_res_4348_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4360_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4361_ = l_Lean_Parser_Attr_simple_parenthesizer___closed__2;
    v___x_4362_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4362_, 0, v___x_4361_);
    crate::leanh::lean_closure_set(v___x_4362_, 1, v___x_4360_);
    return v___x_4362_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4363_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2,
    );
    v___x_4364_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_many_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3,
    );
    v___x_4366_ = l_Lean_Parser_Attr_extern_parenthesizer___closed__1;
    v___x_4367_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4367_, 0, v___x_4366_);
    crate::leanh::lean_closure_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4,
    );
    v___x_4369_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4370_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4371_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___x_4371_, 0, v___x_4370_);
    crate::leanh::lean_closure_set(v___x_4371_, 1, v___x_4369_);
    crate::leanh::lean_closure_set(v___x_4371_, 2, v___x_4368_);
    return v___x_4371_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_parenthesizer(
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = l_Lean_Parser_Attr_extern_parenthesizer___closed__0;
    v___x_4378_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__5_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__5,
    );
    v___x_4379_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4377_,
        v___x_4378_,
        v_a_4372_,
        v_a_4373_,
        v_a_4374_,
        v_a_4375_,
    );
    return v___x_4379_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_parenthesizer___boxed(
    mut v_a_4380_: *mut crate::leanh::LeanObject,
    mut v_a_4381_: *mut crate::leanh::LeanObject,
    mut v_a_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4385_ =
        l_Lean_Parser_Attr_extern_parenthesizer(v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
    crate::leanh::lean_dec(v_a_4383_);
    crate::leanh::lean_dec_ref(v_a_4382_);
    crate::leanh::lean_dec(v_a_4381_);
    crate::leanh::lean_dec_ref(v_a_4380_);
    return v_res_4385_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4394_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4395_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0;
    v___x_4396_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_extern_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4397_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4393_,
        v___x_4394_,
        v___x_4395_,
        v___x_4396_,
    );
    return v___x_4397_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___boxed(
    mut v_a_4398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
    return v_res_4399_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = 0;
    v___x_4407_ = 1;
    v___x_4408_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4409_ = l_Lean_Parser_Attr_tactic__alt___closed__0;
    v___x_4410_ = l_Lean_Parser_mkAntiquot(v___x_4409_, v___x_4408_, v___x_4407_, v___x_4406_);
    return v___x_4410_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lean_Parser_Attr_tactic__alt___closed__0;
    v___x_4412_ = l_Lean_Parser_symbol(v___x_4411_);
    return v___x_4412_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4413_ = l_Lean_Parser_ident;
    v___x_4414_ = l_Lean_Parser_skip;
    v___x_4415_ = l_Lean_Parser_andthen(v___x_4414_, v___x_4413_);
    return v___x_4415_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__4,
    );
    v___x_4417_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__3,
    );
    v___x_4418_ = l_Lean_Parser_andthen(v___x_4417_, v___x_4416_);
    return v___x_4418_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4419_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__5,
    );
    v___x_4420_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4421_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4422_ = l_Lean_Parser_leadingNode(v___x_4421_, v___x_4420_, v___x_4419_);
    return v___x_4422_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__6,
    );
    v___x_4424_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__2,
    );
    v___x_4425_ = l_Lean_Parser_withAntiquot(v___x_4424_, v___x_4423_);
    return v___x_4425_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__7,
    );
    v___x_4427_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4428_ = l_Lean_Parser_withCache(v___x_4427_, v___x_4426_);
    return v___x_4428_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt() -> *mut crate::leanh::LeanObject {
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4429_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__8,
    );
    return v___x_4429_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4431_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4432_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4433_ = l_Lean_Parser_Attr_tactic__alt;
    v___x_4434_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4435_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4431_, v___x_4432_, v___x_4433_, v___x_4434_);
    return v___x_4435_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1___boxed(
    mut v_a_4436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4437_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
    return v_res_4437_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4440_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4441_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0;
    v___x_4442_ = l_Lean_addBuiltinDocString(v___x_4440_, v___x_4441_);
    return v___x_4442_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___boxed(
    mut v_a_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
    return v_res_4444_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4472_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6;
    v___x_4473_ = l_Lean_addBuiltinDeclarationRanges(v___x_4471_, v___x_4472_);
    return v___x_4473_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___boxed(
    mut v_a_4474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4475_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
    return v_res_4475_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_formatter(
    mut v_a_4495_: *mut crate::leanh::LeanObject,
    mut v_a_4496_: *mut crate::leanh::LeanObject,
    mut v_a_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4500_ = l_Lean_Parser_Attr_tactic__alt_formatter___closed__0;
    v___x_4501_ = l_Lean_Parser_Attr_tactic__alt_formatter___closed__4;
    v___x_4502_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4500_,
        v___x_4501_,
        v_a_4495_,
        v_a_4496_,
        v_a_4497_,
        v_a_4498_,
    );
    return v___x_4502_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_formatter___boxed(
    mut v_a_4503_: *mut crate::leanh::LeanObject,
    mut v_a_4504_: *mut crate::leanh::LeanObject,
    mut v_a_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4508_ =
        l_Lean_Parser_Attr_tactic__alt_formatter(v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
    crate::leanh::lean_dec(v_a_4506_);
    crate::leanh::lean_dec_ref(v_a_4505_);
    crate::leanh::lean_dec(v_a_4504_);
    crate::leanh::lean_dec_ref(v_a_4503_);
    return v_res_4508_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4517_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4518_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0;
    v___x_4519_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__alt_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4520_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4516_,
        v___x_4517_,
        v___x_4518_,
        v___x_4519_,
    );
    return v___x_4520_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___boxed(
    mut v_a_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
    return v_res_4522_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_parenthesizer(
    mut v_a_4542_: *mut crate::leanh::LeanObject,
    mut v_a_4543_: *mut crate::leanh::LeanObject,
    mut v_a_4544_: *mut crate::leanh::LeanObject,
    mut v_a_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4547_ = l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0;
    v___x_4548_ = l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4;
    v___x_4549_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4547_,
        v___x_4548_,
        v_a_4542_,
        v_a_4543_,
        v_a_4544_,
        v_a_4545_,
    );
    return v___x_4549_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_parenthesizer___boxed(
    mut v_a_4550_: *mut crate::leanh::LeanObject,
    mut v_a_4551_: *mut crate::leanh::LeanObject,
    mut v_a_4552_: *mut crate::leanh::LeanObject,
    mut v_a_4553_: *mut crate::leanh::LeanObject,
    mut v_a_4554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4555_ =
        l_Lean_Parser_Attr_tactic__alt_parenthesizer(v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
    crate::leanh::lean_dec(v_a_4553_);
    crate::leanh::lean_dec_ref(v_a_4552_);
    crate::leanh::lean_dec(v_a_4551_);
    crate::leanh::lean_dec_ref(v_a_4550_);
    return v_res_4555_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4563_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4564_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4565_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0;
    v___x_4566_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__alt_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4567_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4563_,
        v___x_4564_,
        v___x_4565_,
        v___x_4566_,
    );
    return v___x_4567_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___boxed(
    mut v_a_4568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4569_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
    return v_res_4569_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4576_ = 0;
    v___x_4577_ = 1;
    v___x_4578_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4579_ = l_Lean_Parser_Attr_tactic__tag___closed__0;
    v___x_4580_ = l_Lean_Parser_mkAntiquot(v___x_4579_, v___x_4578_, v___x_4577_, v___x_4576_);
    return v___x_4580_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4581_ = l_Lean_Parser_Attr_tactic__tag___closed__0;
    v___x_4582_ = l_Lean_Parser_symbol(v___x_4581_);
    return v___x_4582_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__4,
    );
    v___x_4584_ = l_Lean_Parser_many1(v___x_4583_);
    return v___x_4584_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4585_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__4,
    );
    v___x_4586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__3,
    );
    v___x_4587_ = l_Lean_Parser_andthen(v___x_4586_, v___x_4585_);
    return v___x_4587_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__5,
    );
    v___x_4589_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4590_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4591_ = l_Lean_Parser_leadingNode(v___x_4590_, v___x_4589_, v___x_4588_);
    return v___x_4591_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__6,
    );
    v___x_4593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__2,
    );
    v___x_4594_ = l_Lean_Parser_withAntiquot(v___x_4593_, v___x_4592_);
    return v___x_4594_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__7,
    );
    v___x_4596_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4597_ = l_Lean_Parser_withCache(v___x_4596_, v___x_4595_);
    return v___x_4597_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag() -> *mut crate::leanh::LeanObject {
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4598_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__8,
    );
    return v___x_4598_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4600_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4601_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4602_ = l_Lean_Parser_Attr_tactic__tag;
    v___x_4603_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4604_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4600_, v___x_4601_, v___x_4602_, v___x_4603_);
    return v___x_4604_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1___boxed(
    mut v_a_4605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4606_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
    return v_res_4606_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4610_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0;
    v___x_4611_ = l_Lean_addBuiltinDocString(v___x_4609_, v___x_4610_);
    return v___x_4611_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___boxed(
    mut v_a_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4613_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
    return v_res_4613_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4640_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4641_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6;
    v___x_4642_ = l_Lean_addBuiltinDeclarationRanges(v___x_4640_, v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___boxed(
    mut v_a_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
    return v_res_4644_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_formatter(
    mut v_a_4663_: *mut crate::leanh::LeanObject,
    mut v_a_4664_: *mut crate::leanh::LeanObject,
    mut v_a_4665_: *mut crate::leanh::LeanObject,
    mut v_a_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4668_ = l_Lean_Parser_Attr_tactic__tag_formatter___closed__0;
    v___x_4669_ = l_Lean_Parser_Attr_tactic__tag_formatter___closed__4;
    v___x_4670_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4668_,
        v___x_4669_,
        v_a_4663_,
        v_a_4664_,
        v_a_4665_,
        v_a_4666_,
    );
    return v___x_4670_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_formatter___boxed(
    mut v_a_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_a_4673_: *mut crate::leanh::LeanObject,
    mut v_a_4674_: *mut crate::leanh::LeanObject,
    mut v_a_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4676_ =
        l_Lean_Parser_Attr_tactic__tag_formatter(v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
    crate::leanh::lean_dec(v_a_4674_);
    crate::leanh::lean_dec_ref(v_a_4673_);
    crate::leanh::lean_dec(v_a_4672_);
    crate::leanh::lean_dec_ref(v_a_4671_);
    return v_res_4676_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4685_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4686_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0;
    v___x_4687_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__tag_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4688_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4684_,
        v___x_4685_,
        v___x_4686_,
        v___x_4687_,
    );
    return v___x_4688_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___boxed(
    mut v_a_4689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
    return v_res_4690_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_parenthesizer(
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4714_ = l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0;
    v___x_4715_ = l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4;
    v___x_4716_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4714_,
        v___x_4715_,
        v_a_4709_,
        v_a_4710_,
        v_a_4711_,
        v_a_4712_,
    );
    return v___x_4716_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_parenthesizer___boxed(
    mut v_a_4717_: *mut crate::leanh::LeanObject,
    mut v_a_4718_: *mut crate::leanh::LeanObject,
    mut v_a_4719_: *mut crate::leanh::LeanObject,
    mut v_a_4720_: *mut crate::leanh::LeanObject,
    mut v_a_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ =
        l_Lean_Parser_Attr_tactic__tag_parenthesizer(v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
    crate::leanh::lean_dec(v_a_4720_);
    crate::leanh::lean_dec_ref(v_a_4719_);
    crate::leanh::lean_dec(v_a_4718_);
    crate::leanh::lean_dec_ref(v_a_4717_);
    return v_res_4722_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4731_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4732_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0;
    v___x_4733_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__tag_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4734_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4730_,
        v___x_4731_,
        v___x_4732_,
        v___x_4733_,
    );
    return v___x_4734_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___boxed(
    mut v_a_4735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4736_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
    return v_res_4736_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4743_: u8 = 0;
    let mut v___x_4744_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4743_ = 0;
    v___x_4744_ = 1;
    v___x_4745_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4746_ = l_Lean_Parser_Attr_tactic__name___closed__0;
    v___x_4747_ = l_Lean_Parser_mkAntiquot(v___x_4746_, v___x_4745_, v___x_4744_, v___x_4743_);
    return v___x_4747_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_Parser_Attr_tactic__name___closed__0;
    v___x_4749_ = l_Lean_Parser_symbol(v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_Parser_strLit;
    v___x_4751_ = l_Lean_Parser_ident;
    v___x_4752_ = l_Lean_Parser_orelse(v___x_4751_, v___x_4750_);
    return v___x_4752_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4753_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__4,
    );
    v___x_4754_ = l_Lean_Parser_skip;
    v___x_4755_ = l_Lean_Parser_andthen(v___x_4754_, v___x_4753_);
    return v___x_4755_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4756_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__5,
    );
    v___x_4757_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__3,
    );
    v___x_4758_ = l_Lean_Parser_andthen(v___x_4757_, v___x_4756_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4759_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__6,
    );
    v___x_4760_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_4761_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4762_ = l_Lean_Parser_leadingNode(v___x_4761_, v___x_4760_, v___x_4759_);
    return v___x_4762_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__7,
    );
    v___x_4764_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__2,
    );
    v___x_4765_ = l_Lean_Parser_withAntiquot(v___x_4764_, v___x_4763_);
    return v___x_4765_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4766_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__8,
    );
    v___x_4767_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4768_ = l_Lean_Parser_withCache(v___x_4767_, v___x_4766_);
    return v___x_4768_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name() -> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__9_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__9,
    );
    return v___x_4769_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4771_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4772_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4773_ = l_Lean_Parser_Attr_tactic__name;
    v___x_4774_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_4775_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4771_, v___x_4772_, v___x_4773_, v___x_4774_);
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1___boxed(
    mut v_a_4776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4777_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
    return v_res_4777_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4780_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4781_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0;
    v___x_4782_ = l_Lean_addBuiltinDocString(v___x_4780_, v___x_4781_);
    return v___x_4782_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___boxed(
    mut v_a_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4784_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
    return v_res_4784_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_formatter(
    mut v_a_4807_: *mut crate::leanh::LeanObject,
    mut v_a_4808_: *mut crate::leanh::LeanObject,
    mut v_a_4809_: *mut crate::leanh::LeanObject,
    mut v_a_4810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4812_ = l_Lean_Parser_Attr_tactic__name_formatter___closed__0;
    v___x_4813_ = l_Lean_Parser_Attr_tactic__name_formatter___closed__5;
    v___x_4814_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(
        v___x_4812_,
        v___x_4813_,
        v_a_4807_,
        v_a_4808_,
        v_a_4809_,
        v_a_4810_,
    );
    return v___x_4814_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_formatter___boxed(
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
    mut v_a_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4820_ =
        l_Lean_Parser_Attr_tactic__name_formatter(v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
    crate::leanh::lean_dec(v_a_4818_);
    crate::leanh::lean_dec_ref(v_a_4817_);
    crate::leanh::lean_dec(v_a_4816_);
    crate::leanh::lean_dec_ref(v_a_4815_);
    return v_res_4820_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4828_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4829_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4830_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0;
    v___x_4831_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__name_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4832_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4828_,
        v___x_4829_,
        v___x_4830_,
        v___x_4831_,
    );
    return v___x_4832_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___boxed(
    mut v_a_4833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4834_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
    return v_res_4834_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_parenthesizer(
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4862_ = l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0;
    v___x_4863_ = l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5;
    v___x_4864_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(
        v___x_4862_,
        v___x_4863_,
        v_a_4857_,
        v_a_4858_,
        v_a_4859_,
        v_a_4860_,
    );
    return v___x_4864_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_parenthesizer___boxed(
    mut v_a_4865_: *mut crate::leanh::LeanObject,
    mut v_a_4866_: *mut crate::leanh::LeanObject,
    mut v_a_4867_: *mut crate::leanh::LeanObject,
    mut v_a_4868_: *mut crate::leanh::LeanObject,
    mut v_a_4869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4870_ =
        l_Lean_Parser_Attr_tactic__name_parenthesizer(v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
    crate::leanh::lean_dec(v_a_4868_);
    crate::leanh::lean_dec_ref(v_a_4867_);
    crate::leanh::lean_dec(v_a_4866_);
    crate::leanh::lean_dec_ref(v_a_4865_);
    return v_res_4870_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4878_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4879_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4880_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0;
    v___x_4881_ = crate::leanh::lean_alloc_closure(
        l_Lean_Parser_Attr_tactic__name_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4882_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4878_,
        v___x_4879_,
        v___x_4880_,
        v___x_4881_,
    );
    return v___x_4882_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___boxed(
    mut v_a_4883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4884_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
    return v_res_4884_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Priority_numPrio = _init_l_Lean_Parser_Priority_numPrio();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Priority_numPrio);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_simple = _init_l_Lean_Parser_Attr_simple();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_simple);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_macro = _init_l_Lean_Parser_Attr_macro();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_macro);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_export = _init_l_Lean_Parser_Attr_export();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_export);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_recursor = _init_l_Lean_Parser_Attr_recursor();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_recursor);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_class = _init_l_Lean_Parser_Attr_class();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_class);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_instance = _init_l_Lean_Parser_Attr_instance();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_instance);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_default__instance = _init_l_Lean_Parser_Attr_default__instance();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_default__instance);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_specialize = _init_l_Lean_Parser_Attr_specialize();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_specialize);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_externEntry = _init_l_Lean_Parser_Attr_externEntry();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_externEntry);
    l_Lean_Parser_Attr_extern = _init_l_Lean_Parser_Attr_extern();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_extern);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__alt = _init_l_Lean_Parser_Attr_tactic__alt();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_tactic__alt);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__tag = _init_l_Lean_Parser_Attr_tactic__tag();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_tactic__tag);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__name = _init_l_Lean_Parser_Attr_tactic__name();
    crate::leanh::lean_mark_persistent(l_Lean_Parser_Attr_tactic__name);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Attr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Parser_Attr(builtin);
}
