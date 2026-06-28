// Lean compiler output
// Module: Lean.Parser.Attr
// Imports: Lean.Parser.Extra
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 112, 114, 105, 111, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,9344938725912493582 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 97, 116, 101, 103, 111, 114, 121, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 105, 111, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11615938313939332388 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,12953954729981012753 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,6386160366488538211 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,16903608221218324827 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__12_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14144577819487878630 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__13_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,12820864901300304239 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__14_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4627047623736319178 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__15_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__16_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,18332721513354491535 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__17_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__18_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,9870152696988459514 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__19_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,14377136827182876443 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__20_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,5381815324804079886 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__21_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11112453953516691050 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,((( 1857506627 as usize) << 1) | 1) as *mut LeanObject,1564673465549365540 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__23_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,12807883410376724107 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__25_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,2138206098876806091 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__27_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,2134880034630724318 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__28_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 114, 105, 111, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__29_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,2249309967286780005 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__30_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,17836958171642591098 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 97, 116, 116, 114, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__0_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,14167642945230817130 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__1_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [97, 116, 116, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11615938313939332388 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,9016880043843696902 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__22_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,((( 249558774 as usize) << 1) | 1) as *mut LeanObject,3781160332249273827 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__4_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__24_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11530201504022192696 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__5_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__26_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,14597782152571136476 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__6_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,9524778246848127557 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__7_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 116, 116, 114, 95, 112, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__8_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,2890506875127363237 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__9_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject,6289677862665402693 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_Parser_Priority_numPrio___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Priority_numPrio___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Priority_numPrio___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Priority_numPrio___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Priority_numPrio: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 114, 105, 111, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 117, 109, 80, 114, 105, 111, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__0_value) as *mut LeanObject,5288000119911482163 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__1_value) as *mut LeanObject,11264383648239794238 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__1_value) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 30 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Priority_numPrio_formatter___closed__0_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Priority_numPrio_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_simple___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_simple___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_simple___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_simple___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_simple___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject,
        3878072352281346923 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_simple___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_simple___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_simple___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_simple___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_simple: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut LeanObject,((( 113 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__1_value) as *mut LeanObject,((( 113 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__4_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_Attr_simple_formatter___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__1_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Attr_simple_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_priorityParser_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__4_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__5_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__6_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__7_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__7_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_formatter___closed__8_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_formatter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [102, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject,3878072352281346923 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,6120378905460204942 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value: LeanClosureObject<0> =
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
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_priorityParser_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_simple_parenthesizer___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 97, 114, 101, 110, 116, 104, 101, 115, 105, 122, 101, 114, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_simple___closed__0_value) as *mut LeanObject,3878072352281346923 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,7229047310583692226 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_macro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_macro___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_macro___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_macro___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_macro___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject,
        5370970300127562257 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_macro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_macro___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_macro___closed__3_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_macro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_macro___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_macro___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_macro___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_macro: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__1_value) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 38 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_formatter___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_formatter___closed__3_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject,5370970300127562257 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,18431002086242330140 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_macro_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_macro_parenthesizer___closed__3_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_macro___closed__0_value) as *mut LeanObject,5370970300127562257 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,11655949949594088000 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_export___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_export___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_export___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_export___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_export___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject,
        8336882369266271787 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_export___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_export___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_export___closed__3_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_export___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_export___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_export___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_export___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_export: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 74 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__1_value) as *mut LeanObject,((( 74 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__4_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_formatter___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_formatter___closed__3_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject,8336882369266271787 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,17544970176348460878 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__3_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_export_parenthesizer___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_export_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_export_parenthesizer___closed__3_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_export___closed__0_value) as *mut LeanObject,8336882369266271787 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,17081142296450615810 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_recursor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_recursor___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_recursor___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject,
        6133751819545484634 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_recursor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_recursor___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_recursor___closed__3_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_recursor___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_recursor___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_recursor___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_recursor___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_recursor: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 101 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__1_value) as *mut LeanObject,((( 101 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__4_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_formatter___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_formatter___closed__3_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject,6133751819545484634 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,932075812504011379 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__3_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_recursor_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_recursor_parenthesizer___closed__3_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_recursor___closed__0_value) as *mut LeanObject,6133751819545484634 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,17060214783765589863 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_class___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_class___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_class___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_class___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_class___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_class___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,
        4629983612007222933 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_class___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_class___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_class___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_class___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_class___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_class___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_class___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_class___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_class: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__1_value) as *mut LeanObject,((( 69 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 43 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__4_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_formatter___closed__2_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_formatter___closed__2_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,4629983612007222933 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,13536653989562982728 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_class_parenthesizer___closed__2_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_class_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_class_parenthesizer___closed__2_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_class___closed__0_value) as *mut LeanObject,4629983612007222933 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,10517532522357765908 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_instance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_instance___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_instance___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_instance___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_instance___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,
        12927425362287788416 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_instance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_instance___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_instance___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_instance___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_instance: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut LeanObject,((( 112 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__1_value) as *mut LeanObject,((( 112 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut LeanObject,((( 37 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__4_value) as *mut LeanObject,((( 37 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__1_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__2_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__3_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__4_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__4_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_formatter___closed__5_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__5_value) as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,12927425362287788416 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,15262820364925198721 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_instance_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__5_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_instance___closed__0_value) as *mut LeanObject,12927425362287788416 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,8038967186449509541 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
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
            100, 101, 102, 97, 117, 108, 116, 95, 105, 110, 115, 116, 97, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_default__instance___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
                as *mut LeanObject,
            8421805314306529249 as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_default__instance___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_default__instance___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_default__instance___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_default__instance: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 138 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__1_value) as *mut LeanObject,((( 138 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__4_value) as *mut LeanObject,((( 43 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_instance_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_formatter___closed__3_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_default__instance_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_formatter___closed__3_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value) as *mut LeanObject,8421805314306529249 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,7711090014203637900 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value: LeanClosureObject<
    4,
> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value: LeanClosureObject<
    2,
> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value: LeanClosureObject<
    2,
> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__1_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_instance_parenthesizer___closed__3_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value: LeanClosureObject<
    3,
> = LeanClosureObject {
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
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__1_value)
            as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__2_value)
            as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance_parenthesizer___closed__3_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_default__instance___closed__0_value) as *mut LeanObject,8421805314306529249 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,652804362000181872 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize___closed__0_value: LeanStringObject<11> =
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
        m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Parser_Attr_specialize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_specialize___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_specialize___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,
        3770768959921593381 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_specialize___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_specialize___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_specialize___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_specialize___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_specialize: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut LeanObject,((( 134 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__1_value) as *mut LeanObject,((( 134 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 46 as usize) << 1) | 1) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__4_value) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__2_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_many_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_formatter___closed__6_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_formatter___closed__6_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,3770768959921593381 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,13290341165972871288 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Priority_numPrio_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_many_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__1_value) as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_specialize_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_specialize_parenthesizer___closed__6_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_specialize___closed__0_value) as *mut LeanObject,3770768959921593381 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,10108530158295159428 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_externEntry___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_externEntry___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut LeanObject,
        13020966400515078259 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_externEntry___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_externEntry___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_externEntry___closed__5_value: LeanStringObject<8> =
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
        m_data: [105, 110, 108, 105, 110, 101, 32, 0],
    };
static mut l_Lean_Parser_Attr_externEntry___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_externEntry___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_externEntry___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_externEntry___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_externEntry: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Parser_Attr_extern___closed__0_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_extern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_extern___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_extern___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_extern___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_extern___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,
        8121184350197546670 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_extern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_extern___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_extern: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut LeanObject,((( 93 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__1_value) as *mut LeanObject,((( 93 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__4_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__2_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__4_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_strLit_formatter___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__6_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__7_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_formatter___closed__8_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_formatter___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__8_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut LeanObject,13020966400515078259 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,16958419729801073126 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_extern_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_formatter___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_extern_formatter___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extern_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_formatter___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_extern_formatter___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_formatter___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_formatter___closed__5: *mut LeanObject = core::ptr::null_mut();
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,8121184350197546670 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,17978558652694071311 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__5_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Parser_strLit_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__8_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry___closed__0_value) as *mut LeanObject,13020966400515078259 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,13755836315023133898 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__1_value) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_extern_parenthesizer___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_extern_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_extern___closed__0_value) as *mut LeanObject,8121184350197546670 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,5066783692093791339 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt___closed__0_value: LeanStringObject<11> =
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
        m_data: [116, 97, 99, 116, 105, 99, 95, 97, 108, 116, 0],
    };
static mut l_Lean_Parser_Attr_tactic__alt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_tactic__alt___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut LeanObject,
        7294395221027647453 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_tactic__alt___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__alt___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__alt___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__alt: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value: LeanStringObject<209> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 209, m_capacity: 209, m_length: 208, m_data: [68, 101, 99, 108, 97, 114, 101, 115, 32, 116, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32, 116, 111, 32, 98, 101, 32, 97, 110, 32, 97, 108, 105, 97, 115, 32, 111, 114, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 102, 111, 114, 109, 32, 111, 102, 32, 97, 110, 32, 101, 120, 105, 115, 116, 105, 110, 103, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 84, 104, 105, 115, 32, 104, 97, 115, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 101, 102, 102, 101, 99, 116, 115, 58, 10, 42, 32, 84, 104, 101, 32, 97, 108, 105, 97, 115, 32, 114, 101, 108, 97, 116, 105, 111, 110, 115, 104, 105, 112, 32, 105, 115, 32, 115, 97, 118, 101, 100, 10, 42, 32, 84, 104, 101, 32, 100, 111, 99, 115, 116, 114, 105, 110, 103, 32, 105, 115, 32, 116, 97, 107, 101, 110, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 111, 114, 105, 103, 105, 110, 97, 108, 32, 116, 97, 99, 116, 105, 99, 44, 32, 105, 102, 32, 112, 114, 101, 115, 101, 110, 116, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 61 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__1_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 60 as usize) << 1) | 1) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__4_value) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut LeanObject,7294395221027647453 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,5315589541704216288 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt___closed__0_value) as *mut LeanObject,7294395221027647453 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,9533205042951121276 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag___closed__0_value: LeanStringObject<11> =
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
        m_data: [116, 97, 99, 116, 105, 99, 95, 116, 97, 103, 0],
    };
static mut l_Lean_Parser_Attr_tactic__tag___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_tactic__tag___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut LeanObject,
        2771816669859235474 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_tactic__tag___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__tag___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__tag___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__tag: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value: LeanStringObject<96> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 96, m_capacity: 96, m_length: 95, m_data: [65, 100, 100, 115, 32, 111, 110, 101, 32, 111, 114, 32, 109, 111, 114, 101, 32, 116, 97, 103, 115, 32, 116, 111, 32, 97, 32, 116, 97, 99, 116, 105, 99, 46, 10, 10, 84, 97, 103, 115, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 116, 104, 101, 32, 99, 97, 110, 111, 110, 105, 99, 97, 108, 32, 110, 97, 109, 101, 115, 32, 102, 111, 114, 32, 116, 97, 99, 116, 105, 99, 115, 46, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 69 as usize) << 1) | 1) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__0_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__1_value) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__3_value) as *mut LeanObject,((( 27 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__4_value) as *mut LeanObject,((( 39 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_many1_formatter___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_formatter___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut LeanObject,2771816669859235474 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,6159138967226915931 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Lean_Parser_many1_parenthesizer___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__alt_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag_parenthesizer___closed__4_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__tag___closed__0_value) as *mut LeanObject,2771816669859235474 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,17214893638470362495 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Parser_Attr_tactic__name___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut LeanObject;
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
pub static l_Lean_Parser_Attr_tactic__name___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut LeanObject,
        744976359190887801 as *mut LeanObject,
    ],
};
static mut l_Lean_Parser_Attr_tactic__name___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value) as *mut LeanObject;
static mut l_Lean_Parser_Attr_tactic__name___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Parser_Attr_tactic__name___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Parser_Attr_tactic__name___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Parser_Attr_tactic__name: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value: LeanStringObject<392> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 392, m_capacity: 392, m_length: 391, m_data: [83, 101, 116, 115, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 46, 10, 10, 79, 114, 100, 105, 110, 97, 114, 105, 108, 121, 44, 32, 116, 97, 99, 116, 105, 99, 32, 110, 97, 109, 101, 115, 32, 97, 114, 101, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 115, 101, 116, 32, 116, 111, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 116, 111, 107, 101, 110, 32, 105, 110, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 112, 97, 114, 115, 101, 114, 46, 32, 73, 102, 32, 116, 104, 105, 115, 10, 112, 114, 111, 99, 101, 115, 115, 32, 102, 97, 105, 108, 115, 44, 32, 111, 114, 32, 105, 102, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 109, 117, 108, 116, 105, 112, 108, 101, 32, 116, 111, 107, 101, 110, 115, 32, 40, 101, 46, 103, 46, 32, 96, 108, 101, 116, 32, 114, 101, 99, 96, 41, 44, 32, 116, 104, 101, 110, 32, 116, 104, 105, 115, 10, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 116, 111, 32, 112, 114, 111, 118, 105, 100, 101, 32, 97, 32, 110, 97, 109, 101, 46, 10, 10, 84, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 110, 97, 109, 101, 32, 105, 115, 32, 117, 115, 101, 100, 32, 105, 110, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 97, 115, 32, 119, 101, 108, 108, 32, 97, 115, 32, 105, 110, 32, 99, 111, 109, 112, 108, 101, 116, 105, 111, 110, 46, 32, 84, 104, 117, 115, 44, 32, 116, 104, 101, 32, 110, 97, 109, 101, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 97, 10, 118, 97, 108, 105, 100, 32, 112, 114, 101, 102, 105, 120, 32, 111, 102, 32, 116, 104, 101, 32, 116, 97, 99, 116, 105, 99, 39, 115, 32, 115, 121, 110, 116, 97, 120, 46, 10, 0]};
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_formatter___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_formatter___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_formatter___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_formatter___closed__5_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut LeanObject,744976359190887801 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__0_value) as *mut LeanObject,4560258218019812116 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0_value) as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value: LeanClosureObject<4> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value: LeanClosureObject<1> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value: LeanClosureObject<2> =
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
        m_fun: l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed
            as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_externEntry_parenthesizer___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_simple_parenthesizer___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value: LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value: LeanClosureObject<3> =
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
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__1_value)
                as *mut LeanObject,
            (((1024 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name_parenthesizer___closed__5_value)
        as *mut LeanObject;
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__2_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__3_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__11_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2__value) as *mut LeanObject,4584992172905639687 as *mut LeanObject] };
static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Parser_Attr_tactic__name___closed__0_value) as *mut LeanObject,744976359190887801 as *mut LeanObject] };
pub static l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__0_value) as *mut LeanObject,6627616489404433736 as *mut LeanObject] };
static mut l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
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
    if lean_obj_tag(v___x_2519_) == 0 {
        let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2519_, 1);
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
    mut v_a_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2524_: *mut LeanObject = core::ptr::null_mut();
    v_res_2524_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
    return v_res_2524_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
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
    if lean_obj_tag(v___x_2556_) == 0 {
        let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2556_, 1);
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
    mut v_a_2560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2561_: *mut LeanObject = core::ptr::null_mut();
    v_res_2561_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
    return v_res_2561_;
}
pub unsafe fn l_Lean_Parser_priorityParser(mut v_rbp_2562_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2563_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2564_ = l_Lean_Parser_categoryParser(v___x_2563_, v_rbp_2562_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_Parser_attrParser(mut v_rbp_2565_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2566_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2567_ = l_Lean_Parser_categoryParser(v___x_2566_, v_rbp_2565_);
    return v___x_2567_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter___redArg(
    mut v_a_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
    mut v_a_2570_: *mut LeanObject,
    mut v_a_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2575_: *mut LeanObject,
    mut v_a_2576_: *mut LeanObject,
    mut v_a_2577_: *mut LeanObject,
    mut v_a_2578_: *mut LeanObject,
    mut v_a_2579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2580_: *mut LeanObject = core::ptr::null_mut();
    v_res_2580_ =
        l_Lean_Parser_priorityParser_formatter___redArg(v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
    lean_dec(v_a_2578_);
    lean_dec_ref(v_a_2577_);
    lean_dec(v_a_2576_);
    lean_dec_ref(v_a_2575_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter(
    mut v_rbp_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ =
        l_Lean_Parser_priorityParser_formatter___redArg(v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
    return v___x_2587_;
}
pub unsafe fn l_Lean_Parser_priorityParser_formatter___boxed(
    mut v_rbp_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
    mut v_a_2591_: *mut LeanObject,
    mut v_a_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2594_: *mut LeanObject = core::ptr::null_mut();
    v_res_2594_ = l_Lean_Parser_priorityParser_formatter(
        v_rbp_2588_,
        v_a_2589_,
        v_a_2590_,
        v_a_2591_,
        v_a_2592_,
    );
    lean_dec(v_a_2592_);
    lean_dec_ref(v_a_2591_);
    lean_dec(v_a_2590_);
    lean_dec_ref(v_a_2589_);
    lean_dec(v_rbp_2588_);
    return v_res_2594_;
}
pub unsafe fn l_Lean_Parser_priorityParser_parenthesizer(
    mut v_rbp_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_rbp_2603_: *mut LeanObject,
    mut v_a_2604_: *mut LeanObject,
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2609_: *mut LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Lean_Parser_priorityParser_parenthesizer(
        v_rbp_2603_,
        v_a_2604_,
        v_a_2605_,
        v_a_2606_,
        v_a_2607_,
    );
    lean_dec(v_a_2607_);
    lean_dec_ref(v_a_2606_);
    lean_dec(v_a_2605_);
    lean_dec_ref(v_a_2604_);
    return v_res_2609_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter___redArg(
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
    mut v_a_2619_: *mut LeanObject,
    mut v_a_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2622_: *mut LeanObject = core::ptr::null_mut();
    v_res_2622_ =
        l_Lean_Parser_attrParser_formatter___redArg(v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_);
    lean_dec(v_a_2620_);
    lean_dec_ref(v_a_2619_);
    lean_dec(v_a_2618_);
    lean_dec_ref(v_a_2617_);
    return v_res_2622_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter(
    mut v_rbp_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    v___x_2629_ =
        l_Lean_Parser_attrParser_formatter___redArg(v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_);
    return v___x_2629_;
}
pub unsafe fn l_Lean_Parser_attrParser_formatter___boxed(
    mut v_rbp_2630_: *mut LeanObject,
    mut v_a_2631_: *mut LeanObject,
    mut v_a_2632_: *mut LeanObject,
    mut v_a_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
    mut v_a_2635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2636_: *mut LeanObject = core::ptr::null_mut();
    v_res_2636_ =
        l_Lean_Parser_attrParser_formatter(v_rbp_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
    lean_dec(v_a_2634_);
    lean_dec_ref(v_a_2633_);
    lean_dec(v_a_2632_);
    lean_dec_ref(v_a_2631_);
    lean_dec(v_rbp_2630_);
    return v_res_2636_;
}
pub unsafe fn l_Lean_Parser_attrParser_parenthesizer(
    mut v_rbp_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_rbp_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
    mut v_a_2648_: *mut LeanObject,
    mut v_a_2649_: *mut LeanObject,
    mut v_a_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2651_: *mut LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Parser_attrParser_parenthesizer(
        v_rbp_2645_,
        v_a_2646_,
        v_a_2647_,
        v_a_2648_,
        v_a_2649_,
    );
    lean_dec(v_a_2649_);
    lean_dec_ref(v_a_2648_);
    lean_dec(v_a_2647_);
    lean_dec_ref(v_a_2646_);
    return v_res_2651_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio___closed__0() -> *mut LeanObject {
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Lean_Parser_maxPrec;
    v___x_2653_ = l_Lean_Parser_checkPrec(v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio___closed__1() -> *mut LeanObject {
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v___x_2654_ = l_Lean_Parser_numLit;
    v___x_2655_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__0_once),
        _init_l_Lean_Parser_Priority_numPrio___closed__0,
    );
    v___x_2656_ = l_Lean_Parser_andthen(v___x_2655_, v___x_2654_);
    return v___x_2656_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio() -> *mut LeanObject {
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    v___x_2657_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Parser_Priority_numPrio___closed__1_once),
        _init_l_Lean_Parser_Priority_numPrio___closed__1,
    );
    return v___x_2657_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1()
-> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2667_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2;
    v___x_2668_ = l_Lean_Parser_Priority_numPrio;
    v___x_2669_ = lean_unsigned_to_nat(1000);
    v___x_2670_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2666_, v___x_2667_, v___x_2668_, v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___boxed(
    mut v_a_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
    return v_res_2672_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3()
-> *mut LeanObject {
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    v___x_2699_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1___closed__2;
    v___x_2700_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___closed__6;
    v___x_2701_ = l_Lean_addBuiltinDeclarationRanges(v___x_2699_, v___x_2700_);
    return v___x_2701_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3___boxed(
    mut v_a_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2703_: *mut LeanObject = core::ptr::null_mut();
    v_res_2703_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
    return v_res_2703_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_formatter(
    mut v_a_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    v___x_2710_ = lean_alloc_closure(
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
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2718_: *mut LeanObject = core::ptr::null_mut();
    v_res_2718_ =
        l_Lean_Parser_Priority_numPrio_formatter(v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
    lean_dec(v_a_2716_);
    lean_dec_ref(v_a_2715_);
    lean_dec(v_a_2714_);
    lean_dec_ref(v_a_2713_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(
    mut v___x_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2725_ =
        l_Lean_PrettyPrinter_Parenthesizer_addPrecCheck___redArg(v___x_2719_, v___y_2721_);
    return v___x_2725_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed(
    mut v___x_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2732_: *mut LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0(
        v___x_2726_,
        v___y_2727_,
        v___y_2728_,
        v___y_2729_,
        v___y_2730_,
    );
    lean_dec(v___y_2730_);
    lean_dec_ref(v___y_2729_);
    lean_dec(v___y_2728_);
    lean_dec_ref(v___y_2727_);
    return v_res_2732_;
}
pub unsafe fn _init_l_Lean_Parser_Priority_numPrio_parenthesizer___closed__0() -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Parser_maxPrec;
    v___f_2734_ = lean_alloc_closure(
        l_Lean_Parser_Priority_numPrio_parenthesizer___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2734_, 0, v___x_2733_);
    return v___f_2734_;
}
pub unsafe fn l_Lean_Parser_Priority_numPrio_parenthesizer(
    mut v_a_2736_: *mut LeanObject,
    mut v_a_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v___f_2741_ = lean_obj_once(
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
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
    mut v_a_2747_: *mut LeanObject,
    mut v_a_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2749_: *mut LeanObject = core::ptr::null_mut();
    v_res_2749_ =
        l_Lean_Parser_Priority_numPrio_parenthesizer(v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
    lean_dec(v_a_2747_);
    lean_dec_ref(v_a_2746_);
    lean_dec(v_a_2745_);
    lean_dec_ref(v_a_2744_);
    return v_res_2749_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__2() -> *mut LeanObject {
    let mut v___x_2756_: u8 = 0;
    let mut v___x_2757_: u8 = 0;
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    v___x_2756_ = 0;
    v___x_2757_ = 1;
    v___x_2758_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2759_ = l_Lean_Parser_Attr_simple___closed__0;
    v___x_2760_ = l_Lean_Parser_mkAntiquot(v___x_2759_, v___x_2758_, v___x_2757_, v___x_2756_);
    return v___x_2760_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__3() -> *mut LeanObject {
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    v___x_2761_ = lean_unsigned_to_nat(0);
    v___x_2762_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__31_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_;
    v___x_2763_ = l_Lean_Parser_categoryParser(v___x_2762_, v___x_2761_);
    return v___x_2763_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__4() -> *mut LeanObject {
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    v___x_2764_ = l_Lean_Parser_ident;
    v___x_2765_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3_once),
        _init_l_Lean_Parser_Attr_simple___closed__3,
    );
    v___x_2766_ = l_Lean_Parser_orelse(v___x_2765_, v___x_2764_);
    return v___x_2766_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__5() -> *mut LeanObject {
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    v___x_2767_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__4_once),
        _init_l_Lean_Parser_Attr_simple___closed__4,
    );
    v___x_2768_ = l_Lean_Parser_skip;
    v___x_2769_ = l_Lean_Parser_andthen(v___x_2768_, v___x_2767_);
    return v___x_2769_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__6() -> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__5_once),
        _init_l_Lean_Parser_Attr_simple___closed__5,
    );
    v___x_2771_ = l_Lean_Parser_optional(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__7() -> *mut LeanObject {
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    v___x_2772_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__6_once),
        _init_l_Lean_Parser_Attr_simple___closed__6,
    );
    v___x_2773_ = l_Lean_Parser_ident;
    v___x_2774_ = l_Lean_Parser_andthen(v___x_2773_, v___x_2772_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__8() -> *mut LeanObject {
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___x_2775_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__7_once),
        _init_l_Lean_Parser_Attr_simple___closed__7,
    );
    v___x_2776_ = lean_unsigned_to_nat(1024);
    v___x_2777_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2778_ = l_Lean_Parser_leadingNode(v___x_2777_, v___x_2776_, v___x_2775_);
    return v___x_2778_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__9() -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__8_once),
        _init_l_Lean_Parser_Attr_simple___closed__8,
    );
    v___x_2780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__2_once),
        _init_l_Lean_Parser_Attr_simple___closed__2,
    );
    v___x_2781_ = l_Lean_Parser_withAntiquot(v___x_2780_, v___x_2779_);
    return v___x_2781_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple___closed__10() -> *mut LeanObject {
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    v___x_2782_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__9_once),
        _init_l_Lean_Parser_Attr_simple___closed__9,
    );
    v___x_2783_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2784_ = l_Lean_Parser_withCache(v___x_2783_, v___x_2782_);
    return v___x_2784_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_simple() -> *mut LeanObject {
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v___x_2785_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__10_once),
        _init_l_Lean_Parser_Attr_simple___closed__10,
    );
    return v___x_2785_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1()
-> *mut LeanObject {
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    v___x_2787_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2788_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2789_ = l_Lean_Parser_Attr_simple;
    v___x_2790_ = lean_unsigned_to_nat(1000);
    v___x_2791_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2787_, v___x_2788_, v___x_2789_, v___x_2790_);
    return v___x_2791_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1___boxed(
    mut v_a_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2793_: *mut LeanObject = core::ptr::null_mut();
    v_res_2793_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
    return v_res_2793_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3()
-> *mut LeanObject {
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    v___x_2820_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2821_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___closed__6;
    v___x_2822_ = l_Lean_addBuiltinDeclarationRanges(v___x_2820_, v___x_2821_);
    return v___x_2822_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3___boxed(
    mut v_a_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2824_: *mut LeanObject = core::ptr::null_mut();
    v_res_2824_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
    return v_res_2824_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter___lam__0(
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    v___x_2830_ = l_Lean_PrettyPrinter_Formatter_pushLine___redArg(v___y_2826_);
    return v___x_2830_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter___lam__0___boxed(
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
    mut v___y_2833_: *mut LeanObject,
    mut v___y_2834_: *mut LeanObject,
    mut v___y_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2836_: *mut LeanObject = core::ptr::null_mut();
    v_res_2836_ = l_Lean_Parser_Attr_simple_formatter___lam__0(
        v___y_2831_,
        v___y_2832_,
        v___y_2833_,
        v___y_2834_,
    );
    lean_dec(v___y_2834_);
    lean_dec_ref(v___y_2833_);
    lean_dec(v___y_2832_);
    lean_dec_ref(v___y_2831_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_formatter(
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
    mut v_a_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2876_: *mut LeanObject = core::ptr::null_mut();
    v_res_2876_ = l_Lean_Parser_Attr_simple_formatter(v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
    lean_dec(v_a_2874_);
    lean_dec_ref(v_a_2873_);
    lean_dec(v_a_2872_);
    lean_dec_ref(v_a_2871_);
    return v_res_2876_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7()
-> *mut LeanObject {
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2885_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_2886_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2887_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7___closed__1;
    v___x_2888_ = lean_alloc_closure(
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
    mut v_a_2890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
    v_res_2891_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
    return v_res_2891_;
}
pub unsafe fn l_Lean_Parser_Attr_simple_parenthesizer(
    mut v_a_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_a_2920_: *mut LeanObject,
    mut v_a_2921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2931_: *mut LeanObject = core::ptr::null_mut();
    v_res_2931_ =
        l_Lean_Parser_Attr_simple_parenthesizer(v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_);
    lean_dec(v_a_2929_);
    lean_dec_ref(v_a_2928_);
    lean_dec(v_a_2927_);
    lean_dec_ref(v_a_2926_);
    return v_res_2931_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_2941_ = l_Lean_Parser_Attr_simple___closed__1;
    v___x_2942_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11___closed__1;
    v___x_2943_ = lean_alloc_closure(
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
    mut v_a_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2946_: *mut LeanObject = core::ptr::null_mut();
    v_res_2946_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
    return v_res_2946_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__2() -> *mut LeanObject {
    let mut v___x_2953_: u8 = 0;
    let mut v___x_2954_: u8 = 0;
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    v___x_2953_ = 0;
    v___x_2954_ = 1;
    v___x_2955_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2956_ = l_Lean_Parser_Attr_macro___closed__0;
    v___x_2957_ = l_Lean_Parser_mkAntiquot(v___x_2956_, v___x_2955_, v___x_2954_, v___x_2953_);
    return v___x_2957_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__4() -> *mut LeanObject {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = l_Lean_Parser_Attr_macro___closed__3;
    v___x_2960_ = l_Lean_Parser_symbol(v___x_2959_);
    return v___x_2960_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__5() -> *mut LeanObject {
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    v___x_2961_ = l_Lean_Parser_ident;
    v___x_2962_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__4_once),
        _init_l_Lean_Parser_Attr_macro___closed__4,
    );
    v___x_2963_ = l_Lean_Parser_andthen(v___x_2962_, v___x_2961_);
    return v___x_2963_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__6() -> *mut LeanObject {
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    v___x_2964_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__5_once),
        _init_l_Lean_Parser_Attr_macro___closed__5,
    );
    v___x_2965_ = lean_unsigned_to_nat(1024);
    v___x_2966_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2967_ = l_Lean_Parser_leadingNode(v___x_2966_, v___x_2965_, v___x_2964_);
    return v___x_2967_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__7() -> *mut LeanObject {
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v___x_2968_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__6_once),
        _init_l_Lean_Parser_Attr_macro___closed__6,
    );
    v___x_2969_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__2_once),
        _init_l_Lean_Parser_Attr_macro___closed__2,
    );
    v___x_2970_ = l_Lean_Parser_withAntiquot(v___x_2969_, v___x_2968_);
    return v___x_2970_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro___closed__8() -> *mut LeanObject {
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2971_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__7_once),
        _init_l_Lean_Parser_Attr_macro___closed__7,
    );
    v___x_2972_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2973_ = l_Lean_Parser_withCache(v___x_2972_, v___x_2971_);
    return v___x_2973_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_macro() -> *mut LeanObject {
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    v___x_2974_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_macro___closed__8_once),
        _init_l_Lean_Parser_Attr_macro___closed__8,
    );
    return v___x_2974_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1()
-> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_2977_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_2978_ = l_Lean_Parser_Attr_macro;
    v___x_2979_ = lean_unsigned_to_nat(1000);
    v___x_2980_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_2976_, v___x_2977_, v___x_2978_, v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1___boxed(
    mut v_a_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2982_: *mut LeanObject = core::ptr::null_mut();
    v_res_2982_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
    return v_res_2982_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3()
-> *mut LeanObject {
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    v___x_3009_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3010_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___closed__6;
    v___x_3011_ = l_Lean_addBuiltinDeclarationRanges(v___x_3009_, v___x_3010_);
    return v___x_3011_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3___boxed(
    mut v_a_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3013_: *mut LeanObject = core::ptr::null_mut();
    v_res_3013_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
    return v_res_3013_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_formatter(
    mut v_a_3030_: *mut LeanObject,
    mut v_a_3031_: *mut LeanObject,
    mut v_a_3032_: *mut LeanObject,
    mut v_a_3033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3038_: *mut LeanObject,
    mut v_a_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
    mut v_a_3042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3043_: *mut LeanObject = core::ptr::null_mut();
    v_res_3043_ = l_Lean_Parser_Attr_macro_formatter(v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_);
    lean_dec(v_a_3041_);
    lean_dec_ref(v_a_3040_);
    lean_dec(v_a_3039_);
    lean_dec_ref(v_a_3038_);
    return v_res_3043_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7()
-> *mut LeanObject {
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3052_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3053_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7___closed__0;
    v___x_3054_ = lean_alloc_closure(
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
    mut v_a_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3057_: *mut LeanObject = core::ptr::null_mut();
    v_res_3057_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
    return v_res_3057_;
}
pub unsafe fn l_Lean_Parser_Attr_macro_parenthesizer(
    mut v_a_3074_: *mut LeanObject,
    mut v_a_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3087_: *mut LeanObject = core::ptr::null_mut();
    v_res_3087_ =
        l_Lean_Parser_Attr_macro_parenthesizer(v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_);
    lean_dec(v_a_3085_);
    lean_dec_ref(v_a_3084_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    return v_res_3087_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    v___x_3095_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3096_ = l_Lean_Parser_Attr_macro___closed__1;
    v___x_3097_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11___closed__0;
    v___x_3098_ = lean_alloc_closure(
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
    mut v_a_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_res_3101_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
    return v_res_3101_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__2() -> *mut LeanObject {
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v___x_3108_ = 0;
    v___x_3109_ = 1;
    v___x_3110_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3111_ = l_Lean_Parser_Attr_export___closed__0;
    v___x_3112_ = l_Lean_Parser_mkAntiquot(v___x_3111_, v___x_3110_, v___x_3109_, v___x_3108_);
    return v___x_3112_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__4() -> *mut LeanObject {
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Parser_Attr_export___closed__3;
    v___x_3115_ = l_Lean_Parser_symbol(v___x_3114_);
    return v___x_3115_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__5() -> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ = l_Lean_Parser_ident;
    v___x_3117_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__4_once),
        _init_l_Lean_Parser_Attr_export___closed__4,
    );
    v___x_3118_ = l_Lean_Parser_andthen(v___x_3117_, v___x_3116_);
    return v___x_3118_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__6() -> *mut LeanObject {
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    v___x_3119_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__5_once),
        _init_l_Lean_Parser_Attr_export___closed__5,
    );
    v___x_3120_ = lean_unsigned_to_nat(1024);
    v___x_3121_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3122_ = l_Lean_Parser_leadingNode(v___x_3121_, v___x_3120_, v___x_3119_);
    return v___x_3122_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__7() -> *mut LeanObject {
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    v___x_3123_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__6_once),
        _init_l_Lean_Parser_Attr_export___closed__6,
    );
    v___x_3124_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__2_once),
        _init_l_Lean_Parser_Attr_export___closed__2,
    );
    v___x_3125_ = l_Lean_Parser_withAntiquot(v___x_3124_, v___x_3123_);
    return v___x_3125_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export___closed__8() -> *mut LeanObject {
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v___x_3126_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__7_once),
        _init_l_Lean_Parser_Attr_export___closed__7,
    );
    v___x_3127_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3128_ = l_Lean_Parser_withCache(v___x_3127_, v___x_3126_);
    return v___x_3128_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_export() -> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_export___closed__8_once),
        _init_l_Lean_Parser_Attr_export___closed__8,
    );
    return v___x_3129_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1()
-> *mut LeanObject {
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3132_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3133_ = l_Lean_Parser_Attr_export;
    v___x_3134_ = lean_unsigned_to_nat(1000);
    v___x_3135_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3131_, v___x_3132_, v___x_3133_, v___x_3134_);
    return v___x_3135_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1___boxed(
    mut v_a_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_res_3137_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
    return v_res_3137_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3()
-> *mut LeanObject {
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    v___x_3164_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3165_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___closed__6;
    v___x_3166_ = l_Lean_addBuiltinDeclarationRanges(v___x_3164_, v___x_3165_);
    return v___x_3166_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3___boxed(
    mut v_a_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3168_: *mut LeanObject = core::ptr::null_mut();
    v_res_3168_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
    return v_res_3168_;
}
pub unsafe fn l_Lean_Parser_Attr_export_formatter(
    mut v_a_3185_: *mut LeanObject,
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3193_: *mut LeanObject,
    mut v_a_3194_: *mut LeanObject,
    mut v_a_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
    mut v_a_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3198_: *mut LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_Parser_Attr_export_formatter(v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
    lean_dec(v_a_3196_);
    lean_dec_ref(v_a_3195_);
    lean_dec(v_a_3194_);
    lean_dec_ref(v_a_3193_);
    return v_res_3198_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7()
-> *mut LeanObject {
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    v___x_3206_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3207_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3208_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7___closed__0;
    v___x_3209_ = lean_alloc_closure(
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
    mut v_a_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3212_: *mut LeanObject = core::ptr::null_mut();
    v_res_3212_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
    return v_res_3212_;
}
pub unsafe fn l_Lean_Parser_Attr_export_parenthesizer(
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
    mut v_a_3231_: *mut LeanObject,
    mut v_a_3232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
    mut v_a_3240_: *mut LeanObject,
    mut v_a_3241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3242_: *mut LeanObject = core::ptr::null_mut();
    v_res_3242_ =
        l_Lean_Parser_Attr_export_parenthesizer(v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
    lean_dec(v_a_3240_);
    lean_dec_ref(v_a_3239_);
    lean_dec(v_a_3238_);
    lean_dec_ref(v_a_3237_);
    return v_res_3242_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3251_ = l_Lean_Parser_Attr_export___closed__1;
    v___x_3252_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11___closed__0;
    v___x_3253_ = lean_alloc_closure(
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
    mut v_a_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3256_: *mut LeanObject = core::ptr::null_mut();
    v_res_3256_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
    return v_res_3256_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__2() -> *mut LeanObject {
    let mut v___x_3263_: u8 = 0;
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = 0;
    v___x_3264_ = 1;
    v___x_3265_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3266_ = l_Lean_Parser_Attr_recursor___closed__0;
    v___x_3267_ = l_Lean_Parser_mkAntiquot(v___x_3266_, v___x_3265_, v___x_3264_, v___x_3263_);
    return v___x_3267_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__4() -> *mut LeanObject {
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    v___x_3269_ = 0;
    v___x_3270_ = l_Lean_Parser_Attr_recursor___closed__3;
    v___x_3271_ = l_Lean_Parser_nonReservedSymbol(v___x_3270_, v___x_3269_);
    return v___x_3271_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__5() -> *mut LeanObject {
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Lean_Parser_numLit;
    v___x_3273_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__4_once),
        _init_l_Lean_Parser_Attr_recursor___closed__4,
    );
    v___x_3274_ = l_Lean_Parser_andthen(v___x_3273_, v___x_3272_);
    return v___x_3274_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__6() -> *mut LeanObject {
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    v___x_3275_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__5_once),
        _init_l_Lean_Parser_Attr_recursor___closed__5,
    );
    v___x_3276_ = lean_unsigned_to_nat(1024);
    v___x_3277_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3278_ = l_Lean_Parser_leadingNode(v___x_3277_, v___x_3276_, v___x_3275_);
    return v___x_3278_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__7() -> *mut LeanObject {
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    v___x_3279_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__6_once),
        _init_l_Lean_Parser_Attr_recursor___closed__6,
    );
    v___x_3280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__2_once),
        _init_l_Lean_Parser_Attr_recursor___closed__2,
    );
    v___x_3281_ = l_Lean_Parser_withAntiquot(v___x_3280_, v___x_3279_);
    return v___x_3281_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor___closed__8() -> *mut LeanObject {
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v___x_3282_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__7_once),
        _init_l_Lean_Parser_Attr_recursor___closed__7,
    );
    v___x_3283_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3284_ = l_Lean_Parser_withCache(v___x_3283_, v___x_3282_);
    return v___x_3284_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_recursor() -> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_recursor___closed__8_once),
        _init_l_Lean_Parser_Attr_recursor___closed__8,
    );
    return v___x_3285_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1()
-> *mut LeanObject {
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    v___x_3287_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3288_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3289_ = l_Lean_Parser_Attr_recursor;
    v___x_3290_ = lean_unsigned_to_nat(1000);
    v___x_3291_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3287_, v___x_3288_, v___x_3289_, v___x_3290_);
    return v___x_3291_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1___boxed(
    mut v_a_3292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3293_: *mut LeanObject = core::ptr::null_mut();
    v_res_3293_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
    return v_res_3293_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3()
-> *mut LeanObject {
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3321_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___closed__6;
    v___x_3322_ = l_Lean_addBuiltinDeclarationRanges(v___x_3320_, v___x_3321_);
    return v___x_3322_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3___boxed(
    mut v_a_3323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3324_: *mut LeanObject = core::ptr::null_mut();
    v_res_3324_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
    return v_res_3324_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_formatter(
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3356_: *mut LeanObject = core::ptr::null_mut();
    v_res_3356_ = l_Lean_Parser_Attr_recursor_formatter(v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_);
    lean_dec(v_a_3354_);
    lean_dec_ref(v_a_3353_);
    lean_dec(v_a_3352_);
    lean_dec_ref(v_a_3351_);
    return v_res_3356_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7()
-> *mut LeanObject {
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    v___x_3364_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3365_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3366_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7___closed__0;
    v___x_3367_ = lean_alloc_closure(
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
    mut v_a_3369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3370_: *mut LeanObject = core::ptr::null_mut();
    v_res_3370_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
    return v_res_3370_;
}
pub unsafe fn l_Lean_Parser_Attr_recursor_parenthesizer(
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
    mut v_a_3401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3402_: *mut LeanObject = core::ptr::null_mut();
    v_res_3402_ =
        l_Lean_Parser_Attr_recursor_parenthesizer(v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
    lean_dec(v_a_3400_);
    lean_dec_ref(v_a_3399_);
    lean_dec(v_a_3398_);
    lean_dec_ref(v_a_3397_);
    return v_res_3402_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3411_ = l_Lean_Parser_Attr_recursor___closed__1;
    v___x_3412_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11___closed__0;
    v___x_3413_ = lean_alloc_closure(
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
    mut v_a_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3416_: *mut LeanObject = core::ptr::null_mut();
    v_res_3416_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
    return v_res_3416_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__2() -> *mut LeanObject {
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3423_ = 0;
    v___x_3424_ = 1;
    v___x_3425_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3426_ = l_Lean_Parser_Attr_class___closed__0;
    v___x_3427_ = l_Lean_Parser_mkAntiquot(v___x_3426_, v___x_3425_, v___x_3424_, v___x_3423_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__3() -> *mut LeanObject {
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    v___x_3428_ = l_Lean_Parser_Attr_class___closed__0;
    v___x_3429_ = l_Lean_Parser_symbol(v___x_3428_);
    return v___x_3429_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__4() -> *mut LeanObject {
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    v___x_3430_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__3_once),
        _init_l_Lean_Parser_Attr_class___closed__3,
    );
    v___x_3431_ = lean_unsigned_to_nat(1024);
    v___x_3432_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3433_ = l_Lean_Parser_leadingNode(v___x_3432_, v___x_3431_, v___x_3430_);
    return v___x_3433_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__5() -> *mut LeanObject {
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3434_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__4_once),
        _init_l_Lean_Parser_Attr_class___closed__4,
    );
    v___x_3435_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__2_once),
        _init_l_Lean_Parser_Attr_class___closed__2,
    );
    v___x_3436_ = l_Lean_Parser_withAntiquot(v___x_3435_, v___x_3434_);
    return v___x_3436_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class___closed__6() -> *mut LeanObject {
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    v___x_3437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__5_once),
        _init_l_Lean_Parser_Attr_class___closed__5,
    );
    v___x_3438_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3439_ = l_Lean_Parser_withCache(v___x_3438_, v___x_3437_);
    return v___x_3439_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_class() -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_class___closed__6_once),
        _init_l_Lean_Parser_Attr_class___closed__6,
    );
    return v___x_3440_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1()
-> *mut LeanObject {
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3442_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3443_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3444_ = l_Lean_Parser_Attr_class;
    v___x_3445_ = lean_unsigned_to_nat(1000);
    v___x_3446_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3442_, v___x_3443_, v___x_3444_, v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1___boxed(
    mut v_a_3447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3448_: *mut LeanObject = core::ptr::null_mut();
    v_res_3448_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
    return v_res_3448_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3()
-> *mut LeanObject {
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    v___x_3475_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3476_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___closed__6;
    v___x_3477_ = l_Lean_addBuiltinDeclarationRanges(v___x_3475_, v___x_3476_);
    return v___x_3477_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3___boxed(
    mut v_a_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3479_: *mut LeanObject = core::ptr::null_mut();
    v_res_3479_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
    return v_res_3479_;
}
pub unsafe fn l_Lean_Parser_Attr_class_formatter(
    mut v_a_3493_: *mut LeanObject,
    mut v_a_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3506_: *mut LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_Parser_Attr_class_formatter(v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
    lean_dec(v_a_3504_);
    lean_dec_ref(v_a_3503_);
    lean_dec(v_a_3502_);
    lean_dec_ref(v_a_3501_);
    return v_res_3506_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7()
-> *mut LeanObject {
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    v___x_3514_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3515_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3516_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7___closed__0;
    v___x_3517_ = lean_alloc_closure(
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
    mut v_a_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3520_: *mut LeanObject = core::ptr::null_mut();
    v_res_3520_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
    return v_res_3520_;
}
pub unsafe fn l_Lean_Parser_Attr_class_parenthesizer(
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
    mut v_a_3544_: *mut LeanObject,
    mut v_a_3545_: *mut LeanObject,
    mut v_a_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3547_: *mut LeanObject = core::ptr::null_mut();
    v_res_3547_ =
        l_Lean_Parser_Attr_class_parenthesizer(v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
    lean_dec(v_a_3545_);
    lean_dec_ref(v_a_3544_);
    lean_dec(v_a_3543_);
    lean_dec_ref(v_a_3542_);
    return v_res_3547_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3556_ = l_Lean_Parser_Attr_class___closed__1;
    v___x_3557_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11___closed__0;
    v___x_3558_ = lean_alloc_closure(
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
    mut v_a_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3561_: *mut LeanObject = core::ptr::null_mut();
    v_res_3561_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
    return v_res_3561_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__2() -> *mut LeanObject {
    let mut v___x_3568_: u8 = 0;
    let mut v___x_3569_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    v___x_3568_ = 0;
    v___x_3569_ = 1;
    v___x_3570_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3571_ = l_Lean_Parser_Attr_instance___closed__0;
    v___x_3572_ = l_Lean_Parser_mkAntiquot(v___x_3571_, v___x_3570_, v___x_3569_, v___x_3568_);
    return v___x_3572_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__3() -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3573_ = l_Lean_Parser_Attr_instance___closed__0;
    v___x_3574_ = l_Lean_Parser_symbol(v___x_3573_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__4() -> *mut LeanObject {
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    v___x_3575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_simple___closed__3_once),
        _init_l_Lean_Parser_Attr_simple___closed__3,
    );
    v___x_3576_ = l_Lean_Parser_skip;
    v___x_3577_ = l_Lean_Parser_andthen(v___x_3576_, v___x_3575_);
    return v___x_3577_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__5() -> *mut LeanObject {
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    v___x_3578_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__4_once),
        _init_l_Lean_Parser_Attr_instance___closed__4,
    );
    v___x_3579_ = l_Lean_Parser_optional(v___x_3578_);
    return v___x_3579_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__6() -> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5_once),
        _init_l_Lean_Parser_Attr_instance___closed__5,
    );
    v___x_3581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__3_once),
        _init_l_Lean_Parser_Attr_instance___closed__3,
    );
    v___x_3582_ = l_Lean_Parser_andthen(v___x_3581_, v___x_3580_);
    return v___x_3582_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__7() -> *mut LeanObject {
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v___x_3583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__6_once),
        _init_l_Lean_Parser_Attr_instance___closed__6,
    );
    v___x_3584_ = lean_unsigned_to_nat(1024);
    v___x_3585_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3586_ = l_Lean_Parser_leadingNode(v___x_3585_, v___x_3584_, v___x_3583_);
    return v___x_3586_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__8() -> *mut LeanObject {
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__7_once),
        _init_l_Lean_Parser_Attr_instance___closed__7,
    );
    v___x_3588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__2_once),
        _init_l_Lean_Parser_Attr_instance___closed__2,
    );
    v___x_3589_ = l_Lean_Parser_withAntiquot(v___x_3588_, v___x_3587_);
    return v___x_3589_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance___closed__9() -> *mut LeanObject {
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    v___x_3590_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__8_once),
        _init_l_Lean_Parser_Attr_instance___closed__8,
    );
    v___x_3591_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3592_ = l_Lean_Parser_withCache(v___x_3591_, v___x_3590_);
    return v___x_3592_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_instance() -> *mut LeanObject {
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    v___x_3593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__9_once),
        _init_l_Lean_Parser_Attr_instance___closed__9,
    );
    return v___x_3593_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1()
-> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3595_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3596_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3597_ = l_Lean_Parser_Attr_instance;
    v___x_3598_ = lean_unsigned_to_nat(1000);
    v___x_3599_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3595_, v___x_3596_, v___x_3597_, v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1___boxed(
    mut v_a_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3601_: *mut LeanObject = core::ptr::null_mut();
    v_res_3601_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
    return v_res_3601_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3()
-> *mut LeanObject {
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    v___x_3628_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3629_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___closed__6;
    v___x_3630_ = l_Lean_addBuiltinDeclarationRanges(v___x_3628_, v___x_3629_);
    return v___x_3630_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3___boxed(
    mut v_a_3631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3632_: *mut LeanObject = core::ptr::null_mut();
    v_res_3632_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
    return v_res_3632_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_formatter(
    mut v_a_3654_: *mut LeanObject,
    mut v_a_3655_: *mut LeanObject,
    mut v_a_3656_: *mut LeanObject,
    mut v_a_3657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3662_: *mut LeanObject,
    mut v_a_3663_: *mut LeanObject,
    mut v_a_3664_: *mut LeanObject,
    mut v_a_3665_: *mut LeanObject,
    mut v_a_3666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3667_: *mut LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lean_Parser_Attr_instance_formatter(v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
    lean_dec(v_a_3665_);
    lean_dec_ref(v_a_3664_);
    lean_dec(v_a_3663_);
    lean_dec_ref(v_a_3662_);
    return v_res_3667_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7()
-> *mut LeanObject {
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    v___x_3675_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3676_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3677_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7___closed__0;
    v___x_3678_ = lean_alloc_closure(
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
    mut v_a_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3681_: *mut LeanObject = core::ptr::null_mut();
    v_res_3681_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
    return v_res_3681_;
}
pub unsafe fn l_Lean_Parser_Attr_instance_parenthesizer(
    mut v_a_3703_: *mut LeanObject,
    mut v_a_3704_: *mut LeanObject,
    mut v_a_3705_: *mut LeanObject,
    mut v_a_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3711_: *mut LeanObject,
    mut v_a_3712_: *mut LeanObject,
    mut v_a_3713_: *mut LeanObject,
    mut v_a_3714_: *mut LeanObject,
    mut v_a_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3716_: *mut LeanObject = core::ptr::null_mut();
    v_res_3716_ =
        l_Lean_Parser_Attr_instance_parenthesizer(v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
    lean_dec(v_a_3714_);
    lean_dec_ref(v_a_3713_);
    lean_dec(v_a_3712_);
    lean_dec_ref(v_a_3711_);
    return v_res_3716_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3725_ = l_Lean_Parser_Attr_instance___closed__1;
    v___x_3726_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11___closed__0;
    v___x_3727_ = lean_alloc_closure(
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
    mut v_a_3729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3730_: *mut LeanObject = core::ptr::null_mut();
    v_res_3730_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
    return v_res_3730_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__2() -> *mut LeanObject {
    let mut v___x_3737_: u8 = 0;
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    v___x_3737_ = 0;
    v___x_3738_ = 1;
    v___x_3739_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3740_ = l_Lean_Parser_Attr_default__instance___closed__0;
    v___x_3741_ = l_Lean_Parser_mkAntiquot(v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_);
    return v___x_3741_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__3() -> *mut LeanObject {
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___x_3742_ = 0;
    v___x_3743_ = l_Lean_Parser_Attr_default__instance___closed__0;
    v___x_3744_ = l_Lean_Parser_nonReservedSymbol(v___x_3743_, v___x_3742_);
    return v___x_3744_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__4() -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_instance___closed__5_once),
        _init_l_Lean_Parser_Attr_instance___closed__5,
    );
    v___x_3746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__3_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__3,
    );
    v___x_3747_ = l_Lean_Parser_andthen(v___x_3746_, v___x_3745_);
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__5() -> *mut LeanObject {
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    v___x_3748_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__4_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__4,
    );
    v___x_3749_ = lean_unsigned_to_nat(1024);
    v___x_3750_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3751_ = l_Lean_Parser_leadingNode(v___x_3750_, v___x_3749_, v___x_3748_);
    return v___x_3751_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__6() -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    v___x_3752_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__5_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__5,
    );
    v___x_3753_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__2_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__2,
    );
    v___x_3754_ = l_Lean_Parser_withAntiquot(v___x_3753_, v___x_3752_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance___closed__7() -> *mut LeanObject {
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3755_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__6_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__6,
    );
    v___x_3756_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3757_ = l_Lean_Parser_withCache(v___x_3756_, v___x_3755_);
    return v___x_3757_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_default__instance() -> *mut LeanObject {
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v___x_3758_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_default__instance___closed__7_once),
        _init_l_Lean_Parser_Attr_default__instance___closed__7,
    );
    return v___x_3758_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1()
-> *mut LeanObject {
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    v___x_3760_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3761_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3762_ = l_Lean_Parser_Attr_default__instance;
    v___x_3763_ = lean_unsigned_to_nat(1000);
    v___x_3764_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3760_, v___x_3761_, v___x_3762_, v___x_3763_);
    return v___x_3764_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1___boxed(
    mut v_a_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
    v_res_3766_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
    return v_res_3766_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3()
-> *mut LeanObject {
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    v___x_3793_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3794_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___closed__6;
    v___x_3795_ = l_Lean_addBuiltinDeclarationRanges(v___x_3793_, v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3___boxed(
    mut v_a_3796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3797_: *mut LeanObject = core::ptr::null_mut();
    v_res_3797_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
    return v_res_3797_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_formatter(
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
    mut v_a_3826_: *mut LeanObject,
    mut v_a_3827_: *mut LeanObject,
    mut v_a_3828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3829_: *mut LeanObject = core::ptr::null_mut();
    v_res_3829_ =
        l_Lean_Parser_Attr_default__instance_formatter(v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
    lean_dec(v_a_3827_);
    lean_dec_ref(v_a_3826_);
    lean_dec(v_a_3825_);
    lean_dec_ref(v_a_3824_);
    return v_res_3829_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7()
-> *mut LeanObject {
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    v___x_3837_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_3838_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3839_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7___closed__0;
    v___x_3840_ = lean_alloc_closure(
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
    mut v_a_3842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3843_: *mut LeanObject = core::ptr::null_mut();
    v_res_3843_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
    return v_res_3843_;
}
pub unsafe fn l_Lean_Parser_Attr_default__instance_parenthesizer(
    mut v_a_3862_: *mut LeanObject,
    mut v_a_3863_: *mut LeanObject,
    mut v_a_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l_Lean_Parser_Attr_default__instance_parenthesizer(
        v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_,
    );
    lean_dec(v_a_3873_);
    lean_dec_ref(v_a_3872_);
    lean_dec(v_a_3871_);
    lean_dec_ref(v_a_3870_);
    return v_res_3875_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_3884_ = l_Lean_Parser_Attr_default__instance___closed__1;
    v___x_3885_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11___closed__0;
    v___x_3886_ = lean_alloc_closure(
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
    mut v_a_3888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3889_: *mut LeanObject = core::ptr::null_mut();
    v_res_3889_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
    return v_res_3889_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__2() -> *mut LeanObject {
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3896_ = 0;
    v___x_3897_ = 1;
    v___x_3898_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3899_ = l_Lean_Parser_Attr_specialize___closed__0;
    v___x_3900_ = l_Lean_Parser_mkAntiquot(v___x_3899_, v___x_3898_, v___x_3897_, v___x_3896_);
    return v___x_3900_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__3() -> *mut LeanObject {
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    v___x_3901_ = 0;
    v___x_3902_ = l_Lean_Parser_Attr_specialize___closed__0;
    v___x_3903_ = l_Lean_Parser_nonReservedSymbol(v___x_3902_, v___x_3901_);
    return v___x_3903_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__4() -> *mut LeanObject {
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    v___x_3904_ = l_Lean_Parser_numLit;
    v___x_3905_ = l_Lean_Parser_ident;
    v___x_3906_ = l_Lean_Parser_orelse(v___x_3905_, v___x_3904_);
    return v___x_3906_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__5() -> *mut LeanObject {
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    v___x_3907_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__4_once),
        _init_l_Lean_Parser_Attr_specialize___closed__4,
    );
    v___x_3908_ = l_Lean_Parser_skip;
    v___x_3909_ = l_Lean_Parser_andthen(v___x_3908_, v___x_3907_);
    return v___x_3909_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__6() -> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__5_once),
        _init_l_Lean_Parser_Attr_specialize___closed__5,
    );
    v___x_3911_ = l_Lean_Parser_many(v___x_3910_);
    return v___x_3911_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__7() -> *mut LeanObject {
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__6_once),
        _init_l_Lean_Parser_Attr_specialize___closed__6,
    );
    v___x_3913_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__3_once),
        _init_l_Lean_Parser_Attr_specialize___closed__3,
    );
    v___x_3914_ = l_Lean_Parser_andthen(v___x_3913_, v___x_3912_);
    return v___x_3914_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__8() -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__7_once),
        _init_l_Lean_Parser_Attr_specialize___closed__7,
    );
    v___x_3916_ = lean_unsigned_to_nat(1024);
    v___x_3917_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3918_ = l_Lean_Parser_leadingNode(v___x_3917_, v___x_3916_, v___x_3915_);
    return v___x_3918_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__9() -> *mut LeanObject {
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    v___x_3919_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__8_once),
        _init_l_Lean_Parser_Attr_specialize___closed__8,
    );
    v___x_3920_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__2_once),
        _init_l_Lean_Parser_Attr_specialize___closed__2,
    );
    v___x_3921_ = l_Lean_Parser_withAntiquot(v___x_3920_, v___x_3919_);
    return v___x_3921_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize___closed__10() -> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__9_once),
        _init_l_Lean_Parser_Attr_specialize___closed__9,
    );
    v___x_3923_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3924_ = l_Lean_Parser_withCache(v___x_3923_, v___x_3922_);
    return v___x_3924_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_specialize() -> *mut LeanObject {
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    v___x_3925_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_specialize___closed__10_once),
        _init_l_Lean_Parser_Attr_specialize___closed__10,
    );
    return v___x_3925_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1()
-> *mut LeanObject {
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3927_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_3928_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3929_ = l_Lean_Parser_Attr_specialize;
    v___x_3930_ = lean_unsigned_to_nat(1000);
    v___x_3931_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_3927_, v___x_3928_, v___x_3929_, v___x_3930_);
    return v___x_3931_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1___boxed(
    mut v_a_3932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3933_: *mut LeanObject = core::ptr::null_mut();
    v_res_3933_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
    return v_res_3933_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3()
-> *mut LeanObject {
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_3961_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___closed__6;
    v___x_3962_ = l_Lean_addBuiltinDeclarationRanges(v___x_3960_, v___x_3961_);
    return v___x_3962_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3___boxed(
    mut v_a_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3964_: *mut LeanObject = core::ptr::null_mut();
    v_res_3964_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
    return v_res_3964_;
}
pub unsafe fn l_Lean_Parser_Attr_specialize_formatter(
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v_a_3993_: *mut LeanObject,
    mut v_a_3994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4004_: *mut LeanObject = core::ptr::null_mut();
    v_res_4004_ =
        l_Lean_Parser_Attr_specialize_formatter(v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_);
    lean_dec(v_a_4002_);
    lean_dec_ref(v_a_4001_);
    lean_dec(v_a_4000_);
    lean_dec_ref(v_a_3999_);
    return v_res_4004_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7()
-> *mut LeanObject {
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    v___x_4012_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4013_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_4014_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7___closed__0;
    v___x_4015_ = lean_alloc_closure(
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
    mut v_a_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
    v_res_4018_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
    return v_res_4018_;
}
pub unsafe fn l_Lean_Parser_Attr_specialize_parenthesizer(
    mut v_a_4045_: *mut LeanObject,
    mut v_a_4046_: *mut LeanObject,
    mut v_a_4047_: *mut LeanObject,
    mut v_a_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4053_: *mut LeanObject,
    mut v_a_4054_: *mut LeanObject,
    mut v_a_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4058_: *mut LeanObject = core::ptr::null_mut();
    v_res_4058_ =
        l_Lean_Parser_Attr_specialize_parenthesizer(v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
    lean_dec(v_a_4056_);
    lean_dec_ref(v_a_4055_);
    lean_dec(v_a_4054_);
    lean_dec_ref(v_a_4053_);
    return v_res_4058_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4066_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4067_ = l_Lean_Parser_Attr_specialize___closed__1;
    v___x_4068_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11___closed__0;
    v___x_4069_ = lean_alloc_closure(
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
    mut v_a_4071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4072_: *mut LeanObject = core::ptr::null_mut();
    v_res_4072_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
    return v_res_4072_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__2() -> *mut LeanObject {
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v___x_4079_ = 0;
    v___x_4080_ = 1;
    v___x_4081_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4082_ = l_Lean_Parser_Attr_externEntry___closed__0;
    v___x_4083_ = l_Lean_Parser_mkAntiquot(v___x_4082_, v___x_4081_, v___x_4080_, v___x_4079_);
    return v___x_4083_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__3() -> *mut LeanObject {
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    v___x_4084_ = l_Lean_Parser_skip;
    v___x_4085_ = l_Lean_Parser_ident;
    v___x_4086_ = l_Lean_Parser_andthen(v___x_4085_, v___x_4084_);
    return v___x_4086_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__4() -> *mut LeanObject {
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    v___x_4087_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__3_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__3,
    );
    v___x_4088_ = l_Lean_Parser_optional(v___x_4087_);
    return v___x_4088_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__6() -> *mut LeanObject {
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v___x_4090_ = 0;
    v___x_4091_ = l_Lean_Parser_Attr_externEntry___closed__5;
    v___x_4092_ = l_Lean_Parser_nonReservedSymbol(v___x_4091_, v___x_4090_);
    return v___x_4092_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__7() -> *mut LeanObject {
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    v___x_4093_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__6_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__6,
    );
    v___x_4094_ = l_Lean_Parser_optional(v___x_4093_);
    return v___x_4094_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__8() -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_Parser_strLit;
    v___x_4096_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__7_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__7,
    );
    v___x_4097_ = l_Lean_Parser_andthen(v___x_4096_, v___x_4095_);
    return v___x_4097_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__9() -> *mut LeanObject {
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    v___x_4098_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__8_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__8,
    );
    v___x_4099_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__4_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__4,
    );
    v___x_4100_ = l_Lean_Parser_andthen(v___x_4099_, v___x_4098_);
    return v___x_4100_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__10() -> *mut LeanObject {
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    v___x_4101_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__9_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__9,
    );
    v___x_4102_ = lean_unsigned_to_nat(1024);
    v___x_4103_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4104_ = l_Lean_Parser_leadingNode(v___x_4103_, v___x_4102_, v___x_4101_);
    return v___x_4104_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__11() -> *mut LeanObject {
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    v___x_4105_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__10_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__10,
    );
    v___x_4106_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__2_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__2,
    );
    v___x_4107_ = l_Lean_Parser_withAntiquot(v___x_4106_, v___x_4105_);
    return v___x_4107_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry___closed__12() -> *mut LeanObject {
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    v___x_4108_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__11_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__11,
    );
    v___x_4109_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4110_ = l_Lean_Parser_withCache(v___x_4109_, v___x_4108_);
    return v___x_4110_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_externEntry() -> *mut LeanObject {
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    v___x_4111_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_externEntry___closed__12_once),
        _init_l_Lean_Parser_Attr_externEntry___closed__12,
    );
    return v___x_4111_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__2() -> *mut LeanObject {
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    v___x_4118_ = 0;
    v___x_4119_ = 1;
    v___x_4120_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4121_ = l_Lean_Parser_Attr_extern___closed__0;
    v___x_4122_ = l_Lean_Parser_mkAntiquot(v___x_4121_, v___x_4120_, v___x_4119_, v___x_4118_);
    return v___x_4122_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__3() -> *mut LeanObject {
    let mut v___x_4123_: u8 = 0;
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v___x_4123_ = 0;
    v___x_4124_ = l_Lean_Parser_Attr_extern___closed__0;
    v___x_4125_ = l_Lean_Parser_nonReservedSymbol(v___x_4124_, v___x_4123_);
    return v___x_4125_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__4() -> *mut LeanObject {
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    v___x_4126_ = l_Lean_Parser_Attr_externEntry;
    v___x_4127_ = l_Lean_Parser_skip;
    v___x_4128_ = l_Lean_Parser_andthen(v___x_4127_, v___x_4126_);
    return v___x_4128_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__5() -> *mut LeanObject {
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    v___x_4129_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__4_once),
        _init_l_Lean_Parser_Attr_extern___closed__4,
    );
    v___x_4130_ = l_Lean_Parser_many(v___x_4129_);
    return v___x_4130_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__6() -> *mut LeanObject {
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    v___x_4131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__5_once),
        _init_l_Lean_Parser_Attr_extern___closed__5,
    );
    v___x_4132_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__3_once),
        _init_l_Lean_Parser_Attr_extern___closed__3,
    );
    v___x_4133_ = l_Lean_Parser_andthen(v___x_4132_, v___x_4131_);
    return v___x_4133_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__7() -> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    v___x_4134_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__6_once),
        _init_l_Lean_Parser_Attr_extern___closed__6,
    );
    v___x_4135_ = lean_unsigned_to_nat(1024);
    v___x_4136_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4137_ = l_Lean_Parser_leadingNode(v___x_4136_, v___x_4135_, v___x_4134_);
    return v___x_4137_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__8() -> *mut LeanObject {
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    v___x_4138_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__7_once),
        _init_l_Lean_Parser_Attr_extern___closed__7,
    );
    v___x_4139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__2_once),
        _init_l_Lean_Parser_Attr_extern___closed__2,
    );
    v___x_4140_ = l_Lean_Parser_withAntiquot(v___x_4139_, v___x_4138_);
    return v___x_4140_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern___closed__9() -> *mut LeanObject {
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    v___x_4141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__8_once),
        _init_l_Lean_Parser_Attr_extern___closed__8,
    );
    v___x_4142_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4143_ = l_Lean_Parser_withCache(v___x_4142_, v___x_4141_);
    return v___x_4143_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern() -> *mut LeanObject {
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_4144_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern___closed__9_once),
        _init_l_Lean_Parser_Attr_extern___closed__9,
    );
    return v___x_4144_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1()
-> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4147_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4148_ = l_Lean_Parser_Attr_extern;
    v___x_4149_ = lean_unsigned_to_nat(1000);
    v___x_4150_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4146_, v___x_4147_, v___x_4148_, v___x_4149_);
    return v___x_4150_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1___boxed(
    mut v_a_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4152_: *mut LeanObject = core::ptr::null_mut();
    v_res_4152_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
    return v_res_4152_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3()
-> *mut LeanObject {
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    v___x_4179_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4180_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___closed__6;
    v___x_4181_ = l_Lean_addBuiltinDeclarationRanges(v___x_4179_, v___x_4180_);
    return v___x_4181_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3___boxed(
    mut v_a_4182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4183_: *mut LeanObject = core::ptr::null_mut();
    v_res_4183_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
    return v_res_4183_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_formatter(
    mut v_a_4213_: *mut LeanObject,
    mut v_a_4214_: *mut LeanObject,
    mut v_a_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4221_: *mut LeanObject,
    mut v_a_4222_: *mut LeanObject,
    mut v_a_4223_: *mut LeanObject,
    mut v_a_4224_: *mut LeanObject,
    mut v_a_4225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4226_: *mut LeanObject = core::ptr::null_mut();
    v_res_4226_ =
        l_Lean_Parser_Attr_externEntry_formatter(v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_);
    lean_dec(v_a_4224_);
    lean_dec_ref(v_a_4223_);
    lean_dec(v_a_4222_);
    lean_dec_ref(v_a_4221_);
    return v_res_4226_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7()
-> *mut LeanObject {
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___x_4234_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4235_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4236_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7___closed__0;
    v___x_4237_ = lean_alloc_closure(
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
    mut v_a_4239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4240_: *mut LeanObject = core::ptr::null_mut();
    v_res_4240_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
    return v_res_4240_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__2() -> *mut LeanObject {
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    v___x_4252_ = lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_formatter___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___f_4253_ = l_Lean_Parser_Attr_simple_formatter___closed__0;
    v___x_4254_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4254_, 0, v___f_4253_);
    lean_closure_set(v___x_4254_, 1, v___x_4252_);
    return v___x_4254_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__3() -> *mut LeanObject {
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    v___x_4255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__2_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__2,
    );
    v___x_4256_ = lean_alloc_closure(
        l_Lean_Parser_many_formatter___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4256_, 0, v___x_4255_);
    return v___x_4256_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__4() -> *mut LeanObject {
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    v___x_4257_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__3_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__3,
    );
    v___x_4258_ = l_Lean_Parser_Attr_extern_formatter___closed__1;
    v___x_4259_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4259_, 0, v___x_4258_);
    lean_closure_set(v___x_4259_, 1, v___x_4257_);
    return v___x_4259_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_formatter___closed__5() -> *mut LeanObject {
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    v___x_4260_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_formatter___closed__4_once),
        _init_l_Lean_Parser_Attr_extern_formatter___closed__4,
    );
    v___x_4261_ = lean_unsigned_to_nat(1024);
    v___x_4262_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4263_ = lean_alloc_closure(
        l_Lean_Parser_leadingNode_formatter___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_4263_, 0, v___x_4262_);
    lean_closure_set(v___x_4263_, 1, v___x_4261_);
    lean_closure_set(v___x_4263_, 2, v___x_4260_);
    return v___x_4263_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_formatter(
    mut v_a_4264_: *mut LeanObject,
    mut v_a_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    v___x_4269_ = l_Lean_Parser_Attr_extern_formatter___closed__0;
    v___x_4270_ = lean_obj_once(
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
    mut v_a_4272_: *mut LeanObject,
    mut v_a_4273_: *mut LeanObject,
    mut v_a_4274_: *mut LeanObject,
    mut v_a_4275_: *mut LeanObject,
    mut v_a_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4277_: *mut LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_Parser_Attr_extern_formatter(v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_);
    lean_dec(v_a_4275_);
    lean_dec_ref(v_a_4274_);
    lean_dec(v_a_4273_);
    lean_dec_ref(v_a_4272_);
    return v_res_4277_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11()
-> *mut LeanObject {
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4286_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4287_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11___closed__0;
    v___x_4288_ = lean_alloc_closure(
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
    mut v_a_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4291_: *mut LeanObject = core::ptr::null_mut();
    v_res_4291_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
    return v_res_4291_;
}
pub unsafe fn l_Lean_Parser_Attr_externEntry_parenthesizer(
    mut v_a_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
    mut v_a_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4329_: *mut LeanObject,
    mut v_a_4330_: *mut LeanObject,
    mut v_a_4331_: *mut LeanObject,
    mut v_a_4332_: *mut LeanObject,
    mut v_a_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4334_: *mut LeanObject = core::ptr::null_mut();
    v_res_4334_ =
        l_Lean_Parser_Attr_externEntry_parenthesizer(v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_);
    lean_dec(v_a_4332_);
    lean_dec_ref(v_a_4331_);
    lean_dec(v_a_4330_);
    lean_dec_ref(v_a_4329_);
    return v_res_4334_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15()
-> *mut LeanObject {
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4343_ = l_Lean_Parser_Attr_externEntry___closed__1;
    v___x_4344_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15___closed__0;
    v___x_4345_ = lean_alloc_closure(
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
    mut v_a_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4348_: *mut LeanObject = core::ptr::null_mut();
    v_res_4348_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
    return v_res_4348_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2() -> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    v___x_4360_ = lean_alloc_closure(
        l_Lean_Parser_Attr_externEntry_parenthesizer___boxed as *mut core::ffi::c_void,
        5,
        0,
    );
    v___x_4361_ = l_Lean_Parser_Attr_simple_parenthesizer___closed__2;
    v___x_4362_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4362_, 0, v___x_4361_);
    lean_closure_set(v___x_4362_, 1, v___x_4360_);
    return v___x_4362_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3() -> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__2_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__2,
    );
    v___x_4364_ = lean_alloc_closure(
        l_Lean_Parser_many_parenthesizer___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4() -> *mut LeanObject {
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    v___x_4365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__3_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__3,
    );
    v___x_4366_ = l_Lean_Parser_Attr_extern_parenthesizer___closed__1;
    v___x_4367_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_4367_, 0, v___x_4366_);
    lean_closure_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__5() -> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_extern_parenthesizer___closed__4_once),
        _init_l_Lean_Parser_Attr_extern_parenthesizer___closed__4,
    );
    v___x_4369_ = lean_unsigned_to_nat(1024);
    v___x_4370_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4371_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Parenthesizer_leadingNode_parenthesizer___boxed
            as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_4371_, 0, v___x_4370_);
    lean_closure_set(v___x_4371_, 1, v___x_4369_);
    lean_closure_set(v___x_4371_, 2, v___x_4368_);
    return v___x_4371_;
}
pub unsafe fn l_Lean_Parser_Attr_extern_parenthesizer(
    mut v_a_4372_: *mut LeanObject,
    mut v_a_4373_: *mut LeanObject,
    mut v_a_4374_: *mut LeanObject,
    mut v_a_4375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = l_Lean_Parser_Attr_extern_parenthesizer___closed__0;
    v___x_4378_ = lean_obj_once(
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
    mut v_a_4380_: *mut LeanObject,
    mut v_a_4381_: *mut LeanObject,
    mut v_a_4382_: *mut LeanObject,
    mut v_a_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4385_: *mut LeanObject = core::ptr::null_mut();
    v_res_4385_ =
        l_Lean_Parser_Attr_extern_parenthesizer(v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_);
    lean_dec(v_a_4383_);
    lean_dec_ref(v_a_4382_);
    lean_dec(v_a_4381_);
    lean_dec_ref(v_a_4380_);
    return v_res_4385_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19()
-> *mut LeanObject {
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    v___x_4393_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4394_ = l_Lean_Parser_Attr_extern___closed__1;
    v___x_4395_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19___closed__0;
    v___x_4396_ = lean_alloc_closure(
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
    mut v_a_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4399_: *mut LeanObject = core::ptr::null_mut();
    v_res_4399_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
    return v_res_4399_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__2() -> *mut LeanObject {
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: u8 = 0;
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    v___x_4406_ = 0;
    v___x_4407_ = 1;
    v___x_4408_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4409_ = l_Lean_Parser_Attr_tactic__alt___closed__0;
    v___x_4410_ = l_Lean_Parser_mkAntiquot(v___x_4409_, v___x_4408_, v___x_4407_, v___x_4406_);
    return v___x_4410_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__3() -> *mut LeanObject {
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lean_Parser_Attr_tactic__alt___closed__0;
    v___x_4412_ = l_Lean_Parser_symbol(v___x_4411_);
    return v___x_4412_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__4() -> *mut LeanObject {
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    v___x_4413_ = l_Lean_Parser_ident;
    v___x_4414_ = l_Lean_Parser_skip;
    v___x_4415_ = l_Lean_Parser_andthen(v___x_4414_, v___x_4413_);
    return v___x_4415_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__5() -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__4,
    );
    v___x_4417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__3,
    );
    v___x_4418_ = l_Lean_Parser_andthen(v___x_4417_, v___x_4416_);
    return v___x_4418_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__6() -> *mut LeanObject {
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    v___x_4419_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__5,
    );
    v___x_4420_ = lean_unsigned_to_nat(1024);
    v___x_4421_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4422_ = l_Lean_Parser_leadingNode(v___x_4421_, v___x_4420_, v___x_4419_);
    return v___x_4422_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__7() -> *mut LeanObject {
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    v___x_4423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__6,
    );
    v___x_4424_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__2,
    );
    v___x_4425_ = l_Lean_Parser_withAntiquot(v___x_4424_, v___x_4423_);
    return v___x_4425_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt___closed__8() -> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    v___x_4426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__7,
    );
    v___x_4427_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4428_ = l_Lean_Parser_withCache(v___x_4427_, v___x_4426_);
    return v___x_4428_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__alt() -> *mut LeanObject {
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    v___x_4429_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__8,
    );
    return v___x_4429_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1()
-> *mut LeanObject {
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    v___x_4431_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4432_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4433_ = l_Lean_Parser_Attr_tactic__alt;
    v___x_4434_ = lean_unsigned_to_nat(1000);
    v___x_4435_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4431_, v___x_4432_, v___x_4433_, v___x_4434_);
    return v___x_4435_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1___boxed(
    mut v_a_4436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4437_: *mut LeanObject = core::ptr::null_mut();
    v_res_4437_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
    return v_res_4437_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3()
-> *mut LeanObject {
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    v___x_4440_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4441_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___closed__0;
    v___x_4442_ = l_Lean_addBuiltinDocString(v___x_4440_, v___x_4441_);
    return v___x_4442_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3___boxed(
    mut v_a_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4444_: *mut LeanObject = core::ptr::null_mut();
    v_res_4444_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
    return v_res_4444_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5()
-> *mut LeanObject {
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4472_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___closed__6;
    v___x_4473_ = l_Lean_addBuiltinDeclarationRanges(v___x_4471_, v___x_4472_);
    return v___x_4473_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5___boxed(
    mut v_a_4474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4475_: *mut LeanObject = core::ptr::null_mut();
    v_res_4475_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
    return v_res_4475_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_formatter(
    mut v_a_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
    mut v_a_4497_: *mut LeanObject,
    mut v_a_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
    mut v_a_4505_: *mut LeanObject,
    mut v_a_4506_: *mut LeanObject,
    mut v_a_4507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4508_: *mut LeanObject = core::ptr::null_mut();
    v_res_4508_ =
        l_Lean_Parser_Attr_tactic__alt_formatter(v_a_4503_, v_a_4504_, v_a_4505_, v_a_4506_);
    lean_dec(v_a_4506_);
    lean_dec_ref(v_a_4505_);
    lean_dec(v_a_4504_);
    lean_dec_ref(v_a_4503_);
    return v_res_4508_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9()
-> *mut LeanObject {
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4517_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4518_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9___closed__0;
    v___x_4519_ = lean_alloc_closure(
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
    mut v_a_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4522_: *mut LeanObject = core::ptr::null_mut();
    v_res_4522_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
    return v_res_4522_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__alt_parenthesizer(
    mut v_a_4542_: *mut LeanObject,
    mut v_a_4543_: *mut LeanObject,
    mut v_a_4544_: *mut LeanObject,
    mut v_a_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4550_: *mut LeanObject,
    mut v_a_4551_: *mut LeanObject,
    mut v_a_4552_: *mut LeanObject,
    mut v_a_4553_: *mut LeanObject,
    mut v_a_4554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4555_: *mut LeanObject = core::ptr::null_mut();
    v_res_4555_ =
        l_Lean_Parser_Attr_tactic__alt_parenthesizer(v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_);
    lean_dec(v_a_4553_);
    lean_dec_ref(v_a_4552_);
    lean_dec(v_a_4551_);
    lean_dec_ref(v_a_4550_);
    return v_res_4555_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13()
-> *mut LeanObject {
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    v___x_4563_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4564_ = l_Lean_Parser_Attr_tactic__alt___closed__1;
    v___x_4565_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13___closed__0;
    v___x_4566_ = lean_alloc_closure(
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
    mut v_a_4568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4569_: *mut LeanObject = core::ptr::null_mut();
    v_res_4569_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
    return v_res_4569_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__2() -> *mut LeanObject {
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    v___x_4576_ = 0;
    v___x_4577_ = 1;
    v___x_4578_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4579_ = l_Lean_Parser_Attr_tactic__tag___closed__0;
    v___x_4580_ = l_Lean_Parser_mkAntiquot(v___x_4579_, v___x_4578_, v___x_4577_, v___x_4576_);
    return v___x_4580_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__3() -> *mut LeanObject {
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    v___x_4581_ = l_Lean_Parser_Attr_tactic__tag___closed__0;
    v___x_4582_ = l_Lean_Parser_symbol(v___x_4581_);
    return v___x_4582_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__4() -> *mut LeanObject {
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    v___x_4583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__alt___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__alt___closed__4,
    );
    v___x_4584_ = l_Lean_Parser_many1(v___x_4583_);
    return v___x_4584_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__5() -> *mut LeanObject {
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    v___x_4585_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__4,
    );
    v___x_4586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__3,
    );
    v___x_4587_ = l_Lean_Parser_andthen(v___x_4586_, v___x_4585_);
    return v___x_4587_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__6() -> *mut LeanObject {
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    v___x_4588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__5,
    );
    v___x_4589_ = lean_unsigned_to_nat(1024);
    v___x_4590_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4591_ = l_Lean_Parser_leadingNode(v___x_4590_, v___x_4589_, v___x_4588_);
    return v___x_4591_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__7() -> *mut LeanObject {
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    v___x_4592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__6,
    );
    v___x_4593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__2,
    );
    v___x_4594_ = l_Lean_Parser_withAntiquot(v___x_4593_, v___x_4592_);
    return v___x_4594_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag___closed__8() -> *mut LeanObject {
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    v___x_4595_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__7,
    );
    v___x_4596_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4597_ = l_Lean_Parser_withCache(v___x_4596_, v___x_4595_);
    return v___x_4597_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__tag() -> *mut LeanObject {
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    v___x_4598_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__tag___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__tag___closed__8,
    );
    return v___x_4598_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1()
-> *mut LeanObject {
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    v___x_4600_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4601_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4602_ = l_Lean_Parser_Attr_tactic__tag;
    v___x_4603_ = lean_unsigned_to_nat(1000);
    v___x_4604_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4600_, v___x_4601_, v___x_4602_, v___x_4603_);
    return v___x_4604_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1___boxed(
    mut v_a_4605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4606_: *mut LeanObject = core::ptr::null_mut();
    v_res_4606_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
    return v_res_4606_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3()
-> *mut LeanObject {
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4610_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___closed__0;
    v___x_4611_ = l_Lean_addBuiltinDocString(v___x_4609_, v___x_4610_);
    return v___x_4611_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3___boxed(
    mut v_a_4612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4613_: *mut LeanObject = core::ptr::null_mut();
    v_res_4613_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
    return v_res_4613_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5()
-> *mut LeanObject {
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    v___x_4640_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4641_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___closed__6;
    v___x_4642_ = l_Lean_addBuiltinDeclarationRanges(v___x_4640_, v___x_4641_);
    return v___x_4642_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5___boxed(
    mut v_a_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4644_: *mut LeanObject = core::ptr::null_mut();
    v_res_4644_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
    return v_res_4644_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_formatter(
    mut v_a_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_a_4665_: *mut LeanObject,
    mut v_a_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4671_: *mut LeanObject,
    mut v_a_4672_: *mut LeanObject,
    mut v_a_4673_: *mut LeanObject,
    mut v_a_4674_: *mut LeanObject,
    mut v_a_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4676_: *mut LeanObject = core::ptr::null_mut();
    v_res_4676_ =
        l_Lean_Parser_Attr_tactic__tag_formatter(v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
    lean_dec(v_a_4674_);
    lean_dec_ref(v_a_4673_);
    lean_dec(v_a_4672_);
    lean_dec_ref(v_a_4671_);
    return v_res_4676_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9()
-> *mut LeanObject {
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v___x_4684_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4685_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4686_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9___closed__0;
    v___x_4687_ = lean_alloc_closure(
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
    mut v_a_4689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4690_: *mut LeanObject = core::ptr::null_mut();
    v_res_4690_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
    return v_res_4690_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__tag_parenthesizer(
    mut v_a_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
    mut v_a_4719_: *mut LeanObject,
    mut v_a_4720_: *mut LeanObject,
    mut v_a_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_res_4722_ =
        l_Lean_Parser_Attr_tactic__tag_parenthesizer(v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
    lean_dec(v_a_4720_);
    lean_dec_ref(v_a_4719_);
    lean_dec(v_a_4718_);
    lean_dec_ref(v_a_4717_);
    return v_res_4722_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13()
-> *mut LeanObject {
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    v___x_4730_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4731_ = l_Lean_Parser_Attr_tactic__tag___closed__1;
    v___x_4732_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13___closed__0;
    v___x_4733_ = lean_alloc_closure(
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
    mut v_a_4735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4736_: *mut LeanObject = core::ptr::null_mut();
    v_res_4736_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
    return v_res_4736_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__2() -> *mut LeanObject {
    let mut v___x_4743_: u8 = 0;
    let mut v___x_4744_: u8 = 0;
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    v___x_4743_ = 0;
    v___x_4744_ = 1;
    v___x_4745_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4746_ = l_Lean_Parser_Attr_tactic__name___closed__0;
    v___x_4747_ = l_Lean_Parser_mkAntiquot(v___x_4746_, v___x_4745_, v___x_4744_, v___x_4743_);
    return v___x_4747_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__3() -> *mut LeanObject {
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_Parser_Attr_tactic__name___closed__0;
    v___x_4749_ = l_Lean_Parser_symbol(v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__4() -> *mut LeanObject {
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    v___x_4750_ = l_Lean_Parser_strLit;
    v___x_4751_ = l_Lean_Parser_ident;
    v___x_4752_ = l_Lean_Parser_orelse(v___x_4751_, v___x_4750_);
    return v___x_4752_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__5() -> *mut LeanObject {
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    v___x_4753_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__4_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__4,
    );
    v___x_4754_ = l_Lean_Parser_skip;
    v___x_4755_ = l_Lean_Parser_andthen(v___x_4754_, v___x_4753_);
    return v___x_4755_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__6() -> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut LeanObject = core::ptr::null_mut();
    v___x_4756_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__5_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__5,
    );
    v___x_4757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__3_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__3,
    );
    v___x_4758_ = l_Lean_Parser_andthen(v___x_4757_, v___x_4756_);
    return v___x_4758_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__7() -> *mut LeanObject {
    let mut v___x_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    v___x_4759_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__6_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__6,
    );
    v___x_4760_ = lean_unsigned_to_nat(1024);
    v___x_4761_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4762_ = l_Lean_Parser_leadingNode(v___x_4761_, v___x_4760_, v___x_4759_);
    return v___x_4762_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__8() -> *mut LeanObject {
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v___x_4763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__7_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__7,
    );
    v___x_4764_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__2_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__2,
    );
    v___x_4765_ = l_Lean_Parser_withAntiquot(v___x_4764_, v___x_4763_);
    return v___x_4765_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name___closed__9() -> *mut LeanObject {
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    v___x_4766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__8_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__8,
    );
    v___x_4767_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4768_ = l_Lean_Parser_withCache(v___x_4767_, v___x_4766_);
    return v___x_4768_;
}
pub unsafe fn _init_l_Lean_Parser_Attr_tactic__name() -> *mut LeanObject {
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    v___x_4769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Parser_Attr_tactic__name___closed__9_once),
        _init_l_Lean_Parser_Attr_tactic__name___closed__9,
    );
    return v___x_4769_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1()
-> *mut LeanObject {
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    v___x_4771_ = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn___closed__10_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_;
    v___x_4772_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4773_ = l_Lean_Parser_Attr_tactic__name;
    v___x_4774_ = lean_unsigned_to_nat(1000);
    v___x_4775_ =
        l_Lean_Parser_addBuiltinLeadingParser(v___x_4771_, v___x_4772_, v___x_4773_, v___x_4774_);
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1___boxed(
    mut v_a_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4777_: *mut LeanObject = core::ptr::null_mut();
    v_res_4777_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
    return v_res_4777_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3()
-> *mut LeanObject {
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    v___x_4780_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4781_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___closed__0;
    v___x_4782_ = l_Lean_addBuiltinDocString(v___x_4780_, v___x_4781_);
    return v___x_4782_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3___boxed(
    mut v_a_4783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4784_: *mut LeanObject = core::ptr::null_mut();
    v_res_4784_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
    return v_res_4784_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_formatter(
    mut v_a_4807_: *mut LeanObject,
    mut v_a_4808_: *mut LeanObject,
    mut v_a_4809_: *mut LeanObject,
    mut v_a_4810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4815_: *mut LeanObject,
    mut v_a_4816_: *mut LeanObject,
    mut v_a_4817_: *mut LeanObject,
    mut v_a_4818_: *mut LeanObject,
    mut v_a_4819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4820_: *mut LeanObject = core::ptr::null_mut();
    v_res_4820_ =
        l_Lean_Parser_Attr_tactic__name_formatter(v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_);
    lean_dec(v_a_4818_);
    lean_dec_ref(v_a_4817_);
    lean_dec(v_a_4816_);
    lean_dec_ref(v_a_4815_);
    return v_res_4820_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7()
-> *mut LeanObject {
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4828_ = l_Lean_PrettyPrinter_formatterAttribute;
    v___x_4829_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4830_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7___closed__0;
    v___x_4831_ = lean_alloc_closure(
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
    mut v_a_4833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4834_: *mut LeanObject = core::ptr::null_mut();
    v_res_4834_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
    return v_res_4834_;
}
pub unsafe fn l_Lean_Parser_Attr_tactic__name_parenthesizer(
    mut v_a_4857_: *mut LeanObject,
    mut v_a_4858_: *mut LeanObject,
    mut v_a_4859_: *mut LeanObject,
    mut v_a_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_4865_: *mut LeanObject,
    mut v_a_4866_: *mut LeanObject,
    mut v_a_4867_: *mut LeanObject,
    mut v_a_4868_: *mut LeanObject,
    mut v_a_4869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4870_: *mut LeanObject = core::ptr::null_mut();
    v_res_4870_ =
        l_Lean_Parser_Attr_tactic__name_parenthesizer(v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
    lean_dec(v_a_4868_);
    lean_dec_ref(v_a_4867_);
    lean_dec(v_a_4866_);
    lean_dec_ref(v_a_4865_);
    return v_res_4870_;
}
pub unsafe fn l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11()
-> *mut LeanObject {
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    v___x_4878_ = l_Lean_PrettyPrinter_parenthesizerAttribute;
    v___x_4879_ = l_Lean_Parser_Attr_tactic__name___closed__1;
    v___x_4880_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11___closed__0;
    v___x_4881_ = lean_alloc_closure(
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
    mut v_a_4883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4884_: *mut LeanObject = core::ptr::null_mut();
    v_res_4884_ = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
    return v_res_4884_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Parser_Attr(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_1857506627____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_initFn_00___x40_Lean_Parser_Attr_249558774____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Priority_numPrio = _init_l_Lean_Parser_Priority_numPrio();
    lean_mark_persistent(l_Lean_Parser_Priority_numPrio);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Priority_numPrio___regBuiltin_Lean_Parser_Priority_numPrio_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_simple = _init_l_Lean_Parser_Attr_simple();
    lean_mark_persistent(l_Lean_Parser_Attr_simple);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_simple___regBuiltin_Lean_Parser_Attr_simple_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_macro = _init_l_Lean_Parser_Attr_macro();
    lean_mark_persistent(l_Lean_Parser_Attr_macro);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_macro___regBuiltin_Lean_Parser_Attr_macro_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_export = _init_l_Lean_Parser_Attr_export();
    lean_mark_persistent(l_Lean_Parser_Attr_export);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_export___regBuiltin_Lean_Parser_Attr_export_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_recursor = _init_l_Lean_Parser_Attr_recursor();
    lean_mark_persistent(l_Lean_Parser_Attr_recursor);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_recursor___regBuiltin_Lean_Parser_Attr_recursor_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_class = _init_l_Lean_Parser_Attr_class();
    lean_mark_persistent(l_Lean_Parser_Attr_class);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_class___regBuiltin_Lean_Parser_Attr_class_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_instance = _init_l_Lean_Parser_Attr_instance();
    lean_mark_persistent(l_Lean_Parser_Attr_instance);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_instance___regBuiltin_Lean_Parser_Attr_instance_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_default__instance = _init_l_Lean_Parser_Attr_default__instance();
    lean_mark_persistent(l_Lean_Parser_Attr_default__instance);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_default__instance___regBuiltin_Lean_Parser_Attr_default__instance_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_specialize = _init_l_Lean_Parser_Attr_specialize();
    lean_mark_persistent(l_Lean_Parser_Attr_specialize);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_specialize___regBuiltin_Lean_Parser_Attr_specialize_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_externEntry = _init_l_Lean_Parser_Attr_externEntry();
    lean_mark_persistent(l_Lean_Parser_Attr_externEntry);
    l_Lean_Parser_Attr_extern = _init_l_Lean_Parser_Attr_extern();
    lean_mark_persistent(l_Lean_Parser_Attr_extern);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_formatter__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_externEntry_parenthesizer__15();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_extern___regBuiltin_Lean_Parser_Attr_extern_parenthesizer__19();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__alt = _init_l_Lean_Parser_Attr_tactic__alt();
    lean_mark_persistent(l_Lean_Parser_Attr_tactic__alt);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_formatter__9();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__alt___regBuiltin_Lean_Parser_Attr_tactic__alt_parenthesizer__13();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__tag = _init_l_Lean_Parser_Attr_tactic__tag();
    lean_mark_persistent(l_Lean_Parser_Attr_tactic__tag);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_declRange__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_formatter__9();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__tag___regBuiltin_Lean_Parser_Attr_tactic__tag_parenthesizer__13();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Parser_Attr_tactic__name = _init_l_Lean_Parser_Attr_tactic__name();
    lean_mark_persistent(l_Lean_Parser_Attr_tactic__name);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_docString__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_formatter__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Parser_Attr_0__Lean_Parser_Attr_tactic__name___regBuiltin_Lean_Parser_Attr_tactic__name_parenthesizer__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Parser_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Parser_Attr(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Parser_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Parser_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Parser_Attr(builtin);
}
