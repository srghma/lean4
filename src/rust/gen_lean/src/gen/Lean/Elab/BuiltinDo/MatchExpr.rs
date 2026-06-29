// Lean compiler output
// Module: Lean.Elab.BuiltinDo.MatchExpr
// Imports: Lean.Elab.Do.Basic Lean.Parser.Do Lean.Elab.Do.PatternVar Lean.Elab.BuiltinDo.Basic Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_size, lean_array_uget,
    lean_array_uset, lean_nat_add, lean_nat_dec_lt, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkIdentFrom};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::{l_Lean_Syntax_setArg, l_Lean_Syntax_setArgs};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Elab::BuiltinDo::Basic::{
    initialize_Lean_Elab_BuiltinDo_Basic, l_Lean_Elab_Do_elabDoIdDecl,
    runtime_initialize_Lean_Elab_BuiltinDo_Basic,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, l_Lean_Elab_Do_DoElemCont_withDuplicableCont,
    l_Lean_Elab_Do_checkMutVarsForShadowing, l_Lean_Elab_Do_doElabToSyntax___redArg,
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_elabDoSeq___boxed,
    l_Lean_Elab_Do_mkMonadApp, runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Do::InferControlInfo::l_Lean_Elab_Do_inferControlInfoElem;
use crate::r#gen::Lean::Elab::Do::PatternVar::{
    initialize_Lean_Elab_Do_PatternVar, l_Lean_Elab_Do_getExprPatternVarsEx___redArg,
    runtime_initialize_Lean_Elab_Do_PatternVar,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabTerm;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_macroAttribute;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 76, 101, 116, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__3_value) as *mut crate::leanh::LeanObject,16509474866657095492 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 80, 97, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__5_value) as *mut crate::leanh::LeanObject,2538307196702464034 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 77, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__7_value) as *mut crate::leanh::LeanObject,11954221159092912200 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 95, 101, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__10_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 65, 108, 116, 115, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__18_value) as *mut crate::leanh::LeanObject,13500049350435642968 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 65, 108, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__20_value) as *mut crate::leanh::LeanObject,4415435816164107676 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 69, 108, 115, 101, 65, 108, 116, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__24_value) as *mut crate::leanh::LeanObject,1632499211127915769 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__26_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [66, 117, 105, 108, 116, 105, 110, 68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__5_value) as *mut crate::leanh::LeanObject,2574759475934501480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [77, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__7_value) as *mut crate::leanh::LeanObject,2365840139019140495 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__8_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,6181302484023352610 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,14827430070762803203 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__3_value) as *mut crate::leanh::LeanObject,12524153255488434229 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__12_value) as *mut crate::leanh::LeanObject,979662948116159977 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 76, 101, 116, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__14_value) as *mut crate::leanh::LeanObject,1715607471448259974 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 111, 76, 101, 116, 77, 101, 116, 97, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__0_value) as *mut crate::leanh::LeanObject,1593954703491519207 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 76, 101, 116, 77, 101, 116, 97, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,3292328894567307887 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [109, 97, 116, 99, 104, 95, 101, 120, 112, 114, 32, 101, 108, 115, 101, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [109, 97, 116, 99, 104, 95, 101, 120, 112, 114, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 95, 120, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__0_value) as *mut crate::leanh::LeanObject,7691542500921366510 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 111, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__2_value) as *mut crate::leanh::LeanObject,5573444893818005634 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__4_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 77, 86, 97, 114, 115, 73, 102, 77, 86, 97, 114, 65, 112, 112, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value) as *mut crate::leanh::LeanObject,3251214244781743540 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__9_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6_value) as *mut crate::leanh::LeanObject,14628847112001182049 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 108, 97, 98, 68, 111, 77, 97, 116, 99, 104, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,15816250570134483916 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(
    mut v_stx_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    v___x_765_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4;
    crate::leanh::lean_inc(v_stx_762_);
    v___x_766_ = l_Lean_Syntax_isOfKind(v_stx_762_, v___x_765_);
    if v___x_766_ == 0 {
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_762_);
        v___x_767_ = l_Lean_Macro_throwUnsupported___redArg(v_a_764_);
        return v___x_767_;
    } else {
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: u8 = 0;
        v___x_768_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_769_ = l_Lean_Syntax_getArg(v_stx_762_, v___x_768_);
        v___x_770_ =
            l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6;
        crate::leanh::lean_inc(v___x_769_);
        v___x_771_ = l_Lean_Syntax_isOfKind(v___x_769_, v___x_770_);
        if v___x_771_ == 0 {
            let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_769_);
            crate::leanh::lean_dec(v_stx_762_);
            v___x_772_ = l_Lean_Macro_throwUnsupported___redArg(v_a_764_);
            return v___x_772_;
        } else {
            let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_775_: u8 = 0;
            v___x_773_ = crate::leanh::lean_unsigned_to_nat(6);
            v___x_774_ = l_Lean_Syntax_getArg(v_stx_762_, v___x_773_);
            crate::leanh::lean_inc(v___x_774_);
            v___x_775_ = l_Lean_Syntax_matchesNull(v___x_774_, v___x_768_);
            if v___x_775_ == 0 {
                let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_774_);
                crate::leanh::lean_dec(v___x_769_);
                crate::leanh::lean_dec(v_stx_762_);
                v___x_776_ = l_Lean_Macro_throwUnsupported___redArg(v_a_764_);
                return v___x_776_;
            } else {
                let mut v_ref_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_784_: u8 = 0;
                let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ref_777_ = crate::leanh::lean_ctor_get(v_a_763_, 5);
                v___x_778_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_779_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_780_ = l_Lean_Syntax_getArg(v_stx_762_, v___x_779_);
                v___x_781_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_782_ = l_Lean_Syntax_getArg(v_stx_762_, v___x_781_);
                crate::leanh::lean_dec(v_stx_762_);
                v___x_783_ = l_Lean_Syntax_getArg(v___x_774_, v___x_778_);
                crate::leanh::lean_dec(v___x_774_);
                v___x_784_ = 0;
                v___x_785_ = l_Lean_SourceInfo_fromRef(v_ref_777_, v___x_784_);
                v___x_786_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8;
                v___x_787_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9;
                crate::leanh::lean_inc_n(v___x_785_, 16);
                v___x_788_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_787_);
                v___x_789_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11;
                v___x_790_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__12;
                v___x_791_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_791_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_791_, 1, v___x_790_);
                v___x_792_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__13;
                v___x_793_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_793_, 1, v___x_792_);
                v___x_794_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__14;
                v___x_795_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_795_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_795_, 1, v___x_794_);
                v___x_796_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__15;
                v___x_797_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_797_, 1, v___x_796_);
                v___x_798_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__16;
                v___x_799_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_799_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_799_, 1, v___x_798_);
                v___x_800_ = l_Lean_Syntax_node5(
                    v___x_785_, v___x_789_, v___x_791_, v___x_793_, v___x_795_, v___x_797_,
                    v___x_799_,
                );
                v___x_801_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17;
                v___x_802_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_802_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
                v___x_803_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19;
                v___x_804_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21;
                v___x_805_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22;
                v___x_806_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_806_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
                v___x_807_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23;
                v___x_808_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_808_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_808_, 1, v___x_807_);
                crate::leanh::lean_inc_ref(v___x_808_);
                crate::leanh::lean_inc_ref(v___x_806_);
                v___x_809_ = l_Lean_Syntax_node4(
                    v___x_785_, v___x_804_, v___x_806_, v___x_769_, v___x_808_, v___x_783_,
                );
                v___x_810_ = l_Lean_Syntax_node1(v___x_785_, v___x_789_, v___x_809_);
                v___x_811_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25;
                v___x_812_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27;
                v___x_813_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28;
                v___x_814_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_814_, 0, v___x_785_);
                crate::leanh::lean_ctor_set(v___x_814_, 1, v___x_813_);
                v___x_815_ = l_Lean_Syntax_node1(v___x_785_, v___x_812_, v___x_814_);
                v___x_816_ = l_Lean_Syntax_node4(
                    v___x_785_, v___x_811_, v___x_806_, v___x_815_, v___x_808_, v___x_782_,
                );
                v___x_817_ = l_Lean_Syntax_node2(v___x_785_, v___x_803_, v___x_810_, v___x_816_);
                v___x_818_ = l_Lean_Syntax_node5(
                    v___x_785_, v___x_786_, v___x_788_, v___x_800_, v___x_780_, v___x_802_,
                    v___x_817_,
                );
                v___x_819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_819_, 0, v___x_818_);
                crate::leanh::lean_ctor_set(v___x_819_, 1, v_a_764_);
                return v___x_819_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed(
    mut v_stx_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr(
        v_stx_820_, v_a_821_, v_a_822_,
    );
    crate::leanh::lean_dec_ref(v_a_821_);
    return v_res_823_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Lean_Elab_macroAttribute;
    v___x_862_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__4;
    v___x_863_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___closed__15;
    v___x_864_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_865_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_861_, v___x_862_, v___x_863_, v___x_864_,
    );
    return v___x_865_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1___boxed(
    mut v_a_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_867_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
    return v_res_867_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(
    mut v_stx_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: u8 = 0;
    v___x_878_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1;
    crate::leanh::lean_inc(v_stx_875_);
    v___x_879_ = l_Lean_Syntax_isOfKind(v_stx_875_, v___x_878_);
    if v___x_879_ == 0 {
        let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_875_);
        v___x_880_ = l_Lean_Macro_throwUnsupported___redArg(v_a_877_);
        return v___x_880_;
    } else {
        let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: u8 = 0;
        v___x_881_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_882_ = l_Lean_Syntax_getArg(v_stx_875_, v___x_881_);
        v___x_883_ =
            l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__6;
        crate::leanh::lean_inc(v___x_882_);
        v___x_884_ = l_Lean_Syntax_isOfKind(v___x_882_, v___x_883_);
        if v___x_884_ == 0 {
            let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_882_);
            crate::leanh::lean_dec(v_stx_875_);
            v___x_885_ = l_Lean_Macro_throwUnsupported___redArg(v_a_877_);
            return v___x_885_;
        } else {
            let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_888_: u8 = 0;
            v___x_886_ = crate::leanh::lean_unsigned_to_nat(6);
            v___x_887_ = l_Lean_Syntax_getArg(v_stx_875_, v___x_886_);
            crate::leanh::lean_inc(v___x_887_);
            v___x_888_ = l_Lean_Syntax_matchesNull(v___x_887_, v___x_881_);
            if v___x_888_ == 0 {
                let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_887_);
                crate::leanh::lean_dec(v___x_882_);
                crate::leanh::lean_dec(v_stx_875_);
                v___x_889_ = l_Lean_Macro_throwUnsupported___redArg(v_a_877_);
                return v___x_889_;
            } else {
                let mut v_ref_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_897_: u8 = 0;
                let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_ref_890_ = crate::leanh::lean_ctor_get(v_a_876_, 5);
                v___x_891_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_892_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_893_ = l_Lean_Syntax_getArg(v_stx_875_, v___x_892_);
                v___x_894_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_895_ = l_Lean_Syntax_getArg(v_stx_875_, v___x_894_);
                crate::leanh::lean_dec(v_stx_875_);
                v___x_896_ = l_Lean_Syntax_getArg(v___x_887_, v___x_891_);
                crate::leanh::lean_dec(v___x_887_);
                v___x_897_ = 0;
                v___x_898_ = l_Lean_SourceInfo_fromRef(v_ref_890_, v___x_897_);
                v___x_899_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8;
                v___x_900_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9;
                crate::leanh::lean_inc_n(v___x_898_, 11);
                v___x_901_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_901_, 1, v___x_900_);
                v___x_902_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11;
                v___x_903_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2_once), _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__2);
                v___x_904_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_904_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_904_, 1, v___x_902_);
                crate::leanh::lean_ctor_set(v___x_904_, 2, v___x_903_);
                v___x_905_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17;
                v___x_906_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_906_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_906_, 1, v___x_905_);
                v___x_907_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__19;
                v___x_908_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21;
                v___x_909_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22;
                v___x_910_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_910_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_910_, 1, v___x_909_);
                v___x_911_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23;
                v___x_912_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_912_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_912_, 1, v___x_911_);
                crate::leanh::lean_inc_ref(v___x_912_);
                crate::leanh::lean_inc_ref(v___x_910_);
                v___x_913_ = l_Lean_Syntax_node4(
                    v___x_898_, v___x_908_, v___x_910_, v___x_882_, v___x_912_, v___x_896_,
                );
                v___x_914_ = l_Lean_Syntax_node1(v___x_898_, v___x_902_, v___x_913_);
                v___x_915_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__25;
                v___x_916_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__27;
                v___x_917_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__28;
                v___x_918_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_898_);
                crate::leanh::lean_ctor_set(v___x_918_, 1, v___x_917_);
                v___x_919_ = l_Lean_Syntax_node1(v___x_898_, v___x_916_, v___x_918_);
                v___x_920_ = l_Lean_Syntax_node4(
                    v___x_898_, v___x_915_, v___x_910_, v___x_919_, v___x_912_, v___x_895_,
                );
                v___x_921_ = l_Lean_Syntax_node2(v___x_898_, v___x_907_, v___x_914_, v___x_920_);
                v___x_922_ = l_Lean_Syntax_node5(
                    v___x_898_, v___x_899_, v___x_901_, v___x_904_, v___x_893_, v___x_906_,
                    v___x_921_,
                );
                v___x_923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_923_, 0, v___x_922_);
                crate::leanh::lean_ctor_set(v___x_923_, 1, v_a_877_);
                return v___x_923_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed(
    mut v_stx_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr(
        v_stx_924_, v_a_925_, v_a_926_,
    );
    crate::leanh::lean_dec_ref(v_a_925_);
    return v_res_927_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l_Lean_Elab_macroAttribute;
    v___x_934_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___closed__1;
    v___x_935_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___closed__1;
    v___x_936_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_937_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_933_, v___x_934_, v___x_935_, v___x_936_,
    );
    return v___x_937_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1___boxed(
    mut v_a_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_939_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
    return v_res_939_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = crate::leanh::lean_box(0);
    v___x_941_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_942_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
    crate::leanh::lean_ctor_set(v___x_942_, 1, v___x_940_);
    return v___x_942_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___closed__0);
    v___x_945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_945_, 0, v___x_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg___boxed(
    mut v___y_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
    return v_res_947_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(
    mut v_00_u03b1_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
    mut v___y_950_: *mut crate::leanh::LeanObject,
    mut v___y_951_: *mut crate::leanh::LeanObject,
    mut v___y_952_: *mut crate::leanh::LeanObject,
    mut v___y_953_: *mut crate::leanh::LeanObject,
    mut v___y_954_: *mut crate::leanh::LeanObject,
    mut v___y_955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
    return v___x_957_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___boxed(
    mut v_00_u03b1_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_967_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0(v_00_u03b1_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
    crate::leanh::lean_dec(v___y_965_);
    crate::leanh::lean_dec_ref(v___y_964_);
    crate::leanh::lean_dec(v___y_963_);
    crate::leanh::lean_dec_ref(v___y_962_);
    crate::leanh::lean_dec(v___y_961_);
    crate::leanh::lean_dec_ref(v___y_960_);
    crate::leanh::lean_dec_ref(v___y_959_);
    return v_res_967_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(
    mut v___x_969_: u8,
    mut v___x_970_: *mut crate::leanh::LeanObject,
    mut v___x_971_: *mut crate::leanh::LeanObject,
    mut v___x_972_: *mut crate::leanh::LeanObject,
    mut v_discr_973_: *mut crate::leanh::LeanObject,
    mut v___x_974_: u8,
    mut v___x_975_: *mut crate::leanh::LeanObject,
    mut v___x_976_: *mut crate::leanh::LeanObject,
    mut v_alts_977_: *mut crate::leanh::LeanObject,
    mut v_altsArr_978_: *mut crate::leanh::LeanObject,
    mut v_rhs_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v_ref_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v___y_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    let mut v_v_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v_v_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut v_unused_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_alts_977_) == 1 {
                    v_info_1023_ = crate::leanh::lean_ctor_get(v_alts_977_, 0);
                    crate::leanh::lean_inc(v_info_1023_);
                    v_kind_1024_ = crate::leanh::lean_ctor_get(v_alts_977_, 1);
                    crate::leanh::lean_inc(v_kind_1024_);
                    v_args_1025_ = crate::leanh::lean_ctor_get(v_alts_977_, 2);
                    crate::leanh::lean_inc_ref(v_args_1025_);
                    v___x_1026_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1027_ = lean_array_get_size(v_args_1025_);
                    v___x_1028_ = lean_nat_dec_lt(v___x_1026_, v___x_1027_);
                    if v___x_1028_ == 0 {
                        crate::leanh::lean_dec_ref(v_altsArr_978_);
                        v___y_1011_ = v_alts_977_;
                        v_info_1012_ = v_info_1023_;
                        v_kind_1013_ = v_kind_1024_;
                        v_args_1014_ = v_args_1025_;
                        state = 4;
                        continue;
                    } else {
                        v_isSharedCheck_1040_ =
                            (!crate::leanh::lean_is_exclusive(v_alts_977_)) as u8;
                        if v_isSharedCheck_1040_ == 0 {
                            v_unused_1041_ = crate::leanh::lean_ctor_get(v_alts_977_, 2);
                            crate::leanh::lean_dec(v_unused_1041_);
                            v_unused_1042_ = crate::leanh::lean_ctor_get(v_alts_977_, 1);
                            crate::leanh::lean_dec(v_unused_1042_);
                            v_unused_1043_ = crate::leanh::lean_ctor_get(v_alts_977_, 0);
                            crate::leanh::lean_dec(v_unused_1043_);
                            v___x_1030_ = v_alts_977_;
                            v_isShared_1031_ = v_isSharedCheck_1040_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_alts_977_);
                            v___x_1030_ = crate::leanh::lean_box(0);
                            v_isShared_1031_ = v_isSharedCheck_1040_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_altsArr_978_);
                    if crate::leanh::lean_obj_tag(v_alts_977_) == 1 {
                        v_info_1044_ = crate::leanh::lean_ctor_get(v_alts_977_, 0);
                        crate::leanh::lean_inc(v_info_1044_);
                        v_kind_1045_ = crate::leanh::lean_ctor_get(v_alts_977_, 1);
                        crate::leanh::lean_inc(v_kind_1045_);
                        v_args_1046_ = crate::leanh::lean_ctor_get(v_alts_977_, 2);
                        crate::leanh::lean_inc_ref(v_args_1046_);
                        v___y_1011_ = v_alts_977_;
                        v_info_1012_ = v_info_1044_;
                        v_kind_1013_ = v_kind_1045_;
                        v_args_1014_ = v_args_1046_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_rhs_979_);
                        v___y_989_ = v_alts_977_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_doBlockResultType_990_ = crate::leanh::lean_ctor_get(v___y_980_, 3);
                crate::leanh::lean_inc_ref(v_doBlockResultType_990_);
                v___x_991_ = l_Lean_Elab_Do_mkMonadApp(
                    v_doBlockResultType_990_,
                    v___y_980_,
                    v___y_981_,
                    v___y_982_,
                    v___y_983_,
                    v___y_984_,
                    v___y_985_,
                    v___y_986_,
                );
                if crate::leanh::lean_obj_tag(v___x_991_) == 0 {
                    v_a_992_ = crate::leanh::lean_ctor_get(v___x_991_, 0);
                    v_isSharedCheck_1009_ = (!crate::leanh::lean_is_exclusive(v___x_991_)) as u8;
                    if v_isSharedCheck_1009_ == 0 {
                        v___x_994_ = v___x_991_;
                        v_isShared_995_ = v_isSharedCheck_1009_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_992_);
                        crate::leanh::lean_dec(v___x_991_);
                        v___x_994_ = crate::leanh::lean_box(0);
                        v_isShared_995_ = v_isSharedCheck_1009_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_989_);
                    crate::leanh::lean_dec(v_discr_973_);
                    crate::leanh::lean_dec_ref(v___x_972_);
                    crate::leanh::lean_dec_ref(v___x_971_);
                    crate::leanh::lean_dec_ref(v___x_970_);
                    return v___x_991_;
                }
            }
            2 => {
                v_ref_996_ = crate::leanh::lean_ctor_get(v___y_985_, 5);
                v___x_997_ = l_Lean_SourceInfo_fromRef(v_ref_996_, v___x_969_);
                v___x_998_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___closed__0;
                v___x_999_ = l_Lean_Name_mkStr4(v___x_970_, v___x_971_, v___x_972_, v___x_998_);
                v___x_1000_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__9;
                crate::leanh::lean_inc_n(v___x_997_, 2);
                v___x_1001_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1001_, 0, v___x_997_);
                crate::leanh::lean_ctor_set(v___x_1001_, 1, v___x_1000_);
                v___x_1002_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__17;
                v___x_1003_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1003_, 0, v___x_997_);
                crate::leanh::lean_ctor_set(v___x_1003_, 1, v___x_1002_);
                v___x_1004_ = l_Lean_Syntax_node4(
                    v___x_997_,
                    v___x_999_,
                    v___x_1001_,
                    v_discr_973_,
                    v___x_1003_,
                    v___y_989_,
                );
                if v_isShared_995_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_994_, 1);
                    v___x_1006_ = v___x_994_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_992_);
                    v___x_1006_ = v_reuseFailAlloc_1008_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1007_ = l_Lean_Elab_Term_elabTerm(
                    v___x_1004_,
                    v___x_1006_,
                    v___x_974_,
                    v___x_974_,
                    v___y_981_,
                    v___y_982_,
                    v___y_983_,
                    v___y_984_,
                    v___y_985_,
                    v___y_986_,
                );
                return v___x_1007_;
            }
            4 => {
                v___x_1015_ = lean_array_get_size(v_args_1014_);
                v___x_1016_ = lean_nat_dec_lt(v___x_975_, v___x_1015_);
                if v___x_1016_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_1014_);
                    crate::leanh::lean_dec(v_kind_1013_);
                    crate::leanh::lean_dec(v_info_1012_);
                    crate::leanh::lean_dec(v_rhs_979_);
                    v___y_989_ = v___y_1011_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1011_);
                    v_v_1017_ = lean_array_fget(v_args_1014_, v___x_975_);
                    v___x_1018_ = crate::leanh::lean_box(0);
                    v_xs_x27_1019_ = lean_array_fset(v_args_1014_, v___x_975_, v___x_1018_);
                    v___x_1020_ = l_Lean_Syntax_setArg(v_v_1017_, v___x_976_, v_rhs_979_);
                    v___x_1021_ = lean_array_fset(v_xs_x27_1019_, v___x_975_, v___x_1020_);
                    v___x_1022_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1022_, 0, v_info_1012_);
                    crate::leanh::lean_ctor_set(v___x_1022_, 1, v_kind_1013_);
                    crate::leanh::lean_ctor_set(v___x_1022_, 2, v___x_1021_);
                    v___y_989_ = v___x_1022_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_v_1032_ = lean_array_fget(v_args_1025_, v___x_1026_);
                v___x_1033_ = crate::leanh::lean_box(0);
                v_xs_x27_1034_ = lean_array_fset(v_args_1025_, v___x_1026_, v___x_1033_);
                v___x_1035_ = l_Lean_Syntax_setArgs(v_v_1032_, v_altsArr_978_);
                v___x_1036_ = lean_array_fset(v_xs_x27_1034_, v___x_1026_, v___x_1035_);
                crate::leanh::lean_inc_ref(v___x_1036_);
                crate::leanh::lean_inc(v_kind_1024_);
                crate::leanh::lean_inc(v_info_1023_);
                if v_isShared_1031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1030_, 2, v___x_1036_);
                    v___x_1038_ = v___x_1030_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_info_1023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_kind_1024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___x_1036_);
                    v___x_1038_ = v_reuseFailAlloc_1039_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1011_ = v___x_1038_;
                v_info_1012_ = v_info_1023_;
                v_kind_1013_ = v_kind_1024_;
                v_args_1014_ = v___x_1036_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_1048_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_1049_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1050_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_discr_1051_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_1052_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_1053_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_1054_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_alts_1055_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_altsArr_1056_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_rhs_1057_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1058_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1059_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1060_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1061_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1062_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1063_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_1064_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_1065_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_7024__boxed_1066_: u8 = 0;
    let mut v___x_7028__boxed_1067_: u8 = 0;
    let mut v_res_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7024__boxed_1066_ = (crate::leanh::lean_unbox(v___x_1047_) as u8);
    v___x_7028__boxed_1067_ = (crate::leanh::lean_unbox(v___x_1052_) as u8);
    v_res_1068_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0(v___x_7024__boxed_1066_, v___x_1048_, v___x_1049_, v___x_1050_, v_discr_1051_, v___x_7028__boxed_1067_, v___x_1053_, v___x_1054_, v_alts_1055_, v_altsArr_1056_, v_rhs_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
    crate::leanh::lean_dec(v___y_1064_);
    crate::leanh::lean_dec_ref(v___y_1063_);
    crate::leanh::lean_dec(v___y_1062_);
    crate::leanh::lean_dec_ref(v___y_1061_);
    crate::leanh::lean_dec(v___y_1060_);
    crate::leanh::lean_dec_ref(v___y_1059_);
    crate::leanh::lean_dec_ref(v___y_1058_);
    crate::leanh::lean_dec(v___x_1054_);
    crate::leanh::lean_dec(v___x_1053_);
    return v_res_1068_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__0;
    v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
    return v___x_1071_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_pattern_1073_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_i_1074_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_1075_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_altsArr_1076_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_discr_1077_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_alts_1078_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_dec_1079_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_rhs_1080_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_1081_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_1082_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_1083_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_1084_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_1085_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_1086_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_1087_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_1088_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1089_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(v___x_1072_, v_pattern_1073_, v_i_1074_, v___x_1075_, v_altsArr_1076_, v_discr_1077_, v_alts_1078_, v_dec_1079_, v_rhs_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
    crate::leanh::lean_dec(v___y_1087_);
    crate::leanh::lean_dec_ref(v___y_1086_);
    crate::leanh::lean_dec(v___y_1085_);
    crate::leanh::lean_dec_ref(v___y_1084_);
    crate::leanh::lean_dec(v___y_1083_);
    crate::leanh::lean_dec_ref(v___y_1082_);
    crate::leanh::lean_dec_ref(v___y_1081_);
    crate::leanh::lean_dec(v___x_1075_);
    crate::leanh::lean_dec(v_i_1074_);
    return v_res_1089_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1091_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__2;
    v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
    return v___x_1092_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(
    mut v_discr_1093_: *mut crate::leanh::LeanObject,
    mut v_alts_1094_: *mut crate::leanh::LeanObject,
    mut v_dec_1095_: *mut crate::leanh::LeanObject,
    mut v_i_1096_: *mut crate::leanh::LeanObject,
    mut v_altsArr_1097_: *mut crate::leanh::LeanObject,
    mut v_a_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: u8 = 0;
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elseSeq_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: u8 = 0;
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: u8 = 0;
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v_a_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1106_ = lean_array_get_size(v_altsArr_1097_);
                v___x_1107_ = lean_nat_dec_lt(v_i_1096_, v___x_1106_);
                if v___x_1107_ == 0 {
                    crate::leanh::lean_dec(v_i_1096_);
                    v___x_1108_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1109_ = l_Lean_Syntax_getArg(v_alts_1094_, v___x_1108_);
                    v___x_1110_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_elseSeq_1111_ = l_Lean_Syntax_getArg(v___x_1109_, v___x_1110_);
                    crate::leanh::lean_dec(v___x_1109_);
                    v___x_1112_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1_once), _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__1);
                    v___x_1113_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__0;
                    v___x_1114_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__1;
                    v___x_1115_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__2;
                    v___x_1116_ = 1;
                    v___x_1117_ = crate::leanh::lean_box((v___x_1107_) as usize);
                    v___x_1118_ = crate::leanh::lean_box((v___x_1116_) as usize);
                    v___f_1119_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__0___boxed as *mut core::ffi::c_void, 19, 10);
                    crate::leanh::lean_closure_set(v___f_1119_, 0, v___x_1117_);
                    crate::leanh::lean_closure_set(v___f_1119_, 1, v___x_1113_);
                    crate::leanh::lean_closure_set(v___f_1119_, 2, v___x_1114_);
                    crate::leanh::lean_closure_set(v___f_1119_, 3, v___x_1115_);
                    crate::leanh::lean_closure_set(v___f_1119_, 4, v_discr_1093_);
                    crate::leanh::lean_closure_set(v___f_1119_, 5, v___x_1118_);
                    crate::leanh::lean_closure_set(v___f_1119_, 6, v___x_1108_);
                    crate::leanh::lean_closure_set(v___f_1119_, 7, v___x_1110_);
                    crate::leanh::lean_closure_set(v___f_1119_, 8, v_alts_1094_);
                    crate::leanh::lean_closure_set(v___f_1119_, 9, v_altsArr_1097_);
                    v___x_1120_ = crate::leanh::lean_box((v___x_1116_) as usize);
                    crate::leanh::lean_inc(v_elseSeq_1111_);
                    v___x_1121_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                        11,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_1121_, 0, v_elseSeq_1111_);
                    crate::leanh::lean_closure_set(v___x_1121_, 1, v_dec_1095_);
                    crate::leanh::lean_closure_set(v___x_1121_, 2, v___x_1120_);
                    v___x_1122_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
                        v___x_1112_,
                        v___x_1121_,
                        v___f_1119_,
                        v_elseSeq_1111_,
                        v_a_1098_,
                        v_a_1099_,
                        v_a_1100_,
                        v_a_1101_,
                        v_a_1102_,
                        v_a_1103_,
                        v_a_1104_,
                    );
                    crate::leanh::lean_dec(v_elseSeq_1111_);
                    return v___x_1122_;
                } else {
                    v___x_1123_ = lean_array_fget(v_altsArr_1097_, v_i_1096_);
                    v___x_1124_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__21;
                    crate::leanh::lean_inc(v___x_1123_);
                    v___x_1125_ = l_Lean_Syntax_isOfKind(v___x_1123_, v___x_1124_);
                    if v___x_1125_ == 0 {
                        crate::leanh::lean_dec(v___x_1123_);
                        crate::leanh::lean_dec_ref(v_altsArr_1097_);
                        crate::leanh::lean_dec(v_i_1096_);
                        crate::leanh::lean_dec_ref(v_dec_1095_);
                        crate::leanh::lean_dec(v_alts_1094_);
                        crate::leanh::lean_dec(v_discr_1093_);
                        v___x_1126_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
                        return v___x_1126_;
                    } else {
                        v___x_1127_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_pattern_1128_ = l_Lean_Syntax_getArg(v___x_1123_, v___x_1127_);
                        crate::leanh::lean_inc(v_pattern_1128_);
                        v___x_1129_ = l_Lean_Elab_Do_getExprPatternVarsEx___redArg(v_pattern_1128_);
                        if crate::leanh::lean_obj_tag(v___x_1129_) == 0 {
                            v_a_1130_ = crate::leanh::lean_ctor_get(v___x_1129_, 0);
                            crate::leanh::lean_inc(v_a_1130_);
                            crate::leanh::lean_dec_ref_known(v___x_1129_, 1);
                            v___x_1131_ = l_Lean_Elab_Do_checkMutVarsForShadowing(
                                v_a_1130_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_,
                                v_a_1103_, v_a_1104_,
                            );
                            crate::leanh::lean_dec(v_a_1130_);
                            if crate::leanh::lean_obj_tag(v___x_1131_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1131_, 1);
                                crate::leanh::lean_inc_ref(v_dec_1095_);
                                crate::leanh::lean_inc(v_pattern_1128_);
                                v___f_1132_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1___boxed as *mut core::ffi::c_void, 17, 8);
                                crate::leanh::lean_closure_set(v___f_1132_, 0, v___x_1124_);
                                crate::leanh::lean_closure_set(v___f_1132_, 1, v_pattern_1128_);
                                crate::leanh::lean_closure_set(v___f_1132_, 2, v_i_1096_);
                                crate::leanh::lean_closure_set(v___f_1132_, 3, v___x_1127_);
                                crate::leanh::lean_closure_set(v___f_1132_, 4, v_altsArr_1097_);
                                crate::leanh::lean_closure_set(v___f_1132_, 5, v_discr_1093_);
                                crate::leanh::lean_closure_set(v___f_1132_, 6, v_alts_1094_);
                                crate::leanh::lean_closure_set(v___f_1132_, 7, v_dec_1095_);
                                v___x_1133_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1134_ = l_Lean_Syntax_getArg(v___x_1123_, v___x_1133_);
                                crate::leanh::lean_dec(v___x_1123_);
                                v___x_1135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3_once), _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___closed__3);
                                v___x_1136_ = l_Lean_MessageData_ofSyntax(v_pattern_1128_);
                                v___x_1137_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1137_, 0, v___x_1135_);
                                crate::leanh::lean_ctor_set(v___x_1137_, 1, v___x_1136_);
                                v___x_1138_ = crate::leanh::lean_box((v___x_1125_) as usize);
                                crate::leanh::lean_inc(v___x_1134_);
                                v___x_1139_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                                    11,
                                    3,
                                );
                                crate::leanh::lean_closure_set(v___x_1139_, 0, v___x_1134_);
                                crate::leanh::lean_closure_set(v___x_1139_, 1, v_dec_1095_);
                                crate::leanh::lean_closure_set(v___x_1139_, 2, v___x_1138_);
                                v___x_1140_ = l_Lean_Elab_Do_doElabToSyntax___redArg(
                                    v___x_1137_,
                                    v___x_1139_,
                                    v___f_1132_,
                                    v___x_1134_,
                                    v_a_1098_,
                                    v_a_1099_,
                                    v_a_1100_,
                                    v_a_1101_,
                                    v_a_1102_,
                                    v_a_1103_,
                                    v_a_1104_,
                                );
                                crate::leanh::lean_dec(v___x_1134_);
                                return v___x_1140_;
                            } else {
                                crate::leanh::lean_dec(v_pattern_1128_);
                                crate::leanh::lean_dec(v___x_1123_);
                                crate::leanh::lean_dec_ref(v_altsArr_1097_);
                                crate::leanh::lean_dec(v_i_1096_);
                                crate::leanh::lean_dec_ref(v_dec_1095_);
                                crate::leanh::lean_dec(v_alts_1094_);
                                crate::leanh::lean_dec(v_discr_1093_);
                                v_a_1141_ = crate::leanh::lean_ctor_get(v___x_1131_, 0);
                                v_isSharedCheck_1148_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1131_)) as u8;
                                if v_isSharedCheck_1148_ == 0 {
                                    v___x_1143_ = v___x_1131_;
                                    v_isShared_1144_ = v_isSharedCheck_1148_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1141_);
                                    crate::leanh::lean_dec(v___x_1131_);
                                    v___x_1143_ = crate::leanh::lean_box(0);
                                    v_isShared_1144_ = v_isSharedCheck_1148_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_pattern_1128_);
                            crate::leanh::lean_dec(v___x_1123_);
                            crate::leanh::lean_dec_ref(v_altsArr_1097_);
                            crate::leanh::lean_dec(v_i_1096_);
                            crate::leanh::lean_dec_ref(v_dec_1095_);
                            crate::leanh::lean_dec(v_alts_1094_);
                            crate::leanh::lean_dec(v_discr_1093_);
                            v_a_1149_ = crate::leanh::lean_ctor_get(v___x_1129_, 0);
                            v_isSharedCheck_1156_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1129_)) as u8;
                            if v_isSharedCheck_1156_ == 0 {
                                v___x_1151_ = v___x_1129_;
                                v_isShared_1152_ = v_isSharedCheck_1156_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1149_);
                                crate::leanh::lean_dec(v___x_1129_);
                                v___x_1151_ = crate::leanh::lean_box(0);
                                v_isShared_1152_ = v_isSharedCheck_1156_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1144_ == 0 {
                    v___x_1146_ = v___x_1143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1146_;
            }
            3 => {
                if v_isShared_1152_ == 0 {
                    v___x_1154_ = v___x_1151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
                    v___x_1154_ = v_reuseFailAlloc_1155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___lam__1(
    mut v___x_1157_: *mut crate::leanh::LeanObject,
    mut v_pattern_1158_: *mut crate::leanh::LeanObject,
    mut v_i_1159_: *mut crate::leanh::LeanObject,
    mut v___x_1160_: *mut crate::leanh::LeanObject,
    mut v_altsArr_1161_: *mut crate::leanh::LeanObject,
    mut v_discr_1162_: *mut crate::leanh::LeanObject,
    mut v_alts_1163_: *mut crate::leanh::LeanObject,
    mut v_dec_1164_: *mut crate::leanh::LeanObject,
    mut v_rhs_1165_: *mut crate::leanh::LeanObject,
    mut v___y_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1174_ = crate::leanh::lean_ctor_get(v___y_1171_, 5);
    v___x_1175_ = 0;
    v___x_1176_ = l_Lean_SourceInfo_fromRef(v_ref_1174_, v___x_1175_);
    v___x_1177_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__22;
    crate::leanh::lean_inc_n(v___x_1176_, 2);
    v___x_1178_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1178_, 0, v___x_1176_);
    crate::leanh::lean_ctor_set(v___x_1178_, 1, v___x_1177_);
    v___x_1179_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__23;
    v___x_1180_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1180_, 0, v___x_1176_);
    crate::leanh::lean_ctor_set(v___x_1180_, 1, v___x_1179_);
    v___x_1181_ = l_Lean_Syntax_node4(
        v___x_1176_,
        v___x_1157_,
        v___x_1178_,
        v_pattern_1158_,
        v___x_1180_,
        v_rhs_1165_,
    );
    v___x_1182_ = lean_nat_add(v_i_1159_, v___x_1160_);
    v___x_1183_ = lean_array_fset(v_altsArr_1161_, v_i_1159_, v___x_1181_);
    v___x_1184_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_1162_, v_alts_1163_, v_dec_1164_, v___x_1182_, v___x_1183_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
    return v___x_1184_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch___boxed(
    mut v_discr_1185_: *mut crate::leanh::LeanObject,
    mut v_alts_1186_: *mut crate::leanh::LeanObject,
    mut v_dec_1187_: *mut crate::leanh::LeanObject,
    mut v_i_1188_: *mut crate::leanh::LeanObject,
    mut v_altsArr_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_1185_, v_alts_1186_, v_dec_1187_, v_i_1188_, v_altsArr_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
    crate::leanh::lean_dec(v_a_1196_);
    crate::leanh::lean_dec_ref(v_a_1195_);
    crate::leanh::lean_dec(v_a_1194_);
    crate::leanh::lean_dec_ref(v_a_1193_);
    crate::leanh::lean_dec(v_a_1192_);
    crate::leanh::lean_dec_ref(v_a_1191_);
    crate::leanh::lean_dec_ref(v_a_1190_);
    return v_res_1198_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(
    mut v_sz_1199_: usize,
    mut v_i_1200_: usize,
    mut v_bs_1201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: u8 = 0;
    let mut v_v_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: usize = 0;
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1202_ = lean_usize_dec_lt(v_i_1200_, v_sz_1199_);
                if v___x_1202_ == 0 {
                    return v_bs_1201_;
                } else {
                    v_v_1203_ = lean_array_uget(v_bs_1201_, v_i_1200_);
                    v___x_1204_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1205_ = lean_array_uset(v_bs_1201_, v_i_1200_, v___x_1204_);
                    v___x_1206_ = 1usize;
                    v___x_1207_ = lean_usize_add(v_i_1200_, v___x_1206_);
                    v___x_1208_ = lean_array_uset(v_bs_x27_1205_, v_i_1200_, v_v_1203_);
                    v_i_1200_ = v___x_1207_;
                    v_bs_1201_ = v___x_1208_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0___boxed(
    mut v_sz_1210_: *mut crate::leanh::LeanObject,
    mut v_i_1211_: *mut crate::leanh::LeanObject,
    mut v_bs_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1213_: usize = 0;
    let mut v_i_boxed_1214_: usize = 0;
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1213_ = crate::leanh::lean_unbox_usize(v_sz_1210_);
    crate::leanh::lean_dec(v_sz_1210_);
    v_i_boxed_1214_ = crate::leanh::lean_unbox_usize(v_i_1211_);
    crate::leanh::lean_dec(v_i_1211_);
    v_res_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(v_sz_boxed_1213_, v_i_boxed_1214_, v_bs_1212_);
    return v_res_1215_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(
    mut v_alts_1216_: *mut crate::leanh::LeanObject,
    mut v_discr_1217_: *mut crate::leanh::LeanObject,
    mut v_dec_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1230_: usize = 0;
    let mut v___x_1231_: usize = 0;
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1228_ = l_Lean_Syntax_getArg(v_alts_1216_, v___x_1227_);
    v___x_1229_ = l_Lean_Syntax_getArgs(v___x_1228_);
    crate::leanh::lean_dec(v___x_1228_);
    v_sz_1230_ = lean_array_size(v___x_1229_);
    v___x_1231_ = 0usize;
    v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_spec__0(v_sz_1230_, v___x_1231_, v___x_1229_);
    v___x_1233_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch(v_discr_1217_, v_alts_1216_, v_dec_1218_, v___x_1227_, v___x_1232_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
    return v___x_1233_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed(
    mut v_alts_1234_: *mut crate::leanh::LeanObject,
    mut v_discr_1235_: *mut crate::leanh::LeanObject,
    mut v_dec_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1245_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0(v_alts_1234_, v_discr_1235_, v_dec_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    crate::leanh::lean_dec(v___y_1241_);
    crate::leanh::lean_dec_ref(v___y_1240_);
    crate::leanh::lean_dec(v___y_1239_);
    crate::leanh::lean_dec_ref(v___y_1238_);
    crate::leanh::lean_dec_ref(v___y_1237_);
    return v_res_1245_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(
    mut v_info_1246_: *mut crate::leanh::LeanObject,
    mut v_discr_1247_: *mut crate::leanh::LeanObject,
    mut v_alts_1248_: *mut crate::leanh::LeanObject,
    mut v_dec_1249_: *mut crate::leanh::LeanObject,
    mut v_a_1250_: *mut crate::leanh::LeanObject,
    mut v_a_1251_: *mut crate::leanh::LeanObject,
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1258_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
    crate::leanh::lean_closure_set(v___f_1258_, 0, v_alts_1248_);
    crate::leanh::lean_closure_set(v___f_1258_, 1, v_discr_1247_);
    v___x_1259_ = l_Lean_Elab_Do_DoElemCont_withDuplicableCont(
        v_dec_1249_,
        v_info_1246_,
        v___f_1258_,
        v_a_1250_,
        v_a_1251_,
        v_a_1252_,
        v_a_1253_,
        v_a_1254_,
        v_a_1255_,
        v_a_1256_,
    );
    return v___x_1259_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed(
    mut v_info_1260_: *mut crate::leanh::LeanObject,
    mut v_discr_1261_: *mut crate::leanh::LeanObject,
    mut v_alts_1262_: *mut crate::leanh::LeanObject,
    mut v_dec_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1272_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_info_1260_, v_discr_1261_, v_alts_1262_, v_dec_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
    crate::leanh::lean_dec(v_a_1270_);
    crate::leanh::lean_dec_ref(v_a_1269_);
    crate::leanh::lean_dec(v_a_1268_);
    crate::leanh::lean_dec_ref(v_a_1267_);
    crate::leanh::lean_dec(v_a_1266_);
    crate::leanh::lean_dec_ref(v_a_1265_);
    crate::leanh::lean_dec_ref(v_a_1264_);
    return v_res_1272_;
}
pub unsafe fn _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1289_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__6;
    v___x_1290_ = l_String_toRawSubstring_x27(v___x_1289_);
    return v___x_1290_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(
    mut v_stx_1304_: *mut crate::leanh::LeanObject,
    mut v_dec_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v_metaFalseTk_x3f_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1359_: u8 = 0;
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1363_: u8 = 0;
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metaFalseTk_x3f_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1314_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8;
                crate::leanh::lean_inc(v_stx_1304_);
                v___x_1315_ = l_Lean_Syntax_isOfKind(v_stx_1304_, v___x_1314_);
                if v___x_1315_ == 0 {
                    crate::leanh::lean_dec_ref(v_dec_1305_);
                    crate::leanh::lean_dec(v_stx_1304_);
                    v___x_1373_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
                    return v___x_1373_;
                } else {
                    v___x_1374_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1375_ = l_Lean_Syntax_getArg(v_stx_1304_, v___x_1374_);
                    v___x_1376_ = l_Lean_Syntax_isNone(v___x_1375_);
                    if v___x_1376_ == 0 {
                        v___x_1377_ = crate::leanh::lean_unsigned_to_nat(5);
                        crate::leanh::lean_inc(v___x_1375_);
                        v___x_1378_ = l_Lean_Syntax_matchesNull(v___x_1375_, v___x_1377_);
                        if v___x_1378_ == 0 {
                            crate::leanh::lean_dec(v___x_1375_);
                            crate::leanh::lean_dec_ref(v_dec_1305_);
                            crate::leanh::lean_dec(v_stx_1304_);
                            v___x_1379_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta_elabMatch_spec__0___redArg();
                            return v___x_1379_;
                        } else {
                            v___x_1380_ = crate::leanh::lean_unsigned_to_nat(4);
                            v_metaFalseTk_x3f_1381_ =
                                l_Lean_Syntax_getArg(v___x_1375_, v___x_1380_);
                            crate::leanh::lean_dec(v___x_1375_);
                            v___x_1382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1382_, 0, v_metaFalseTk_x3f_1381_);
                            v_metaFalseTk_x3f_1317_ = v___x_1382_;
                            v___y_1318_ = v_a_1306_;
                            v___y_1319_ = v_a_1307_;
                            v___y_1320_ = v_a_1308_;
                            v___y_1321_ = v_a_1309_;
                            v___y_1322_ = v_a_1310_;
                            v___y_1323_ = v_a_1311_;
                            v___y_1324_ = v_a_1312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1375_);
                        v___x_1383_ = crate::leanh::lean_box(0);
                        v_metaFalseTk_x3f_1317_ = v___x_1383_;
                        v___y_1318_ = v_a_1306_;
                        v___y_1319_ = v_a_1307_;
                        v___y_1320_ = v_a_1308_;
                        v___y_1321_ = v_a_1309_;
                        v___y_1322_ = v_a_1310_;
                        v___y_1323_ = v_a_1311_;
                        v___y_1324_ = v_a_1312_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_stx_1304_);
                v___x_1325_ = l_Lean_Elab_Do_inferControlInfoElem(
                    v_stx_1304_,
                    v___y_1319_,
                    v___y_1320_,
                    v___y_1321_,
                    v___y_1322_,
                    v___y_1323_,
                    v___y_1324_,
                );
                if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    crate::leanh::lean_inc(v_a_1326_);
                    crate::leanh::lean_dec_ref_known(v___x_1325_, 1);
                    v___x_1327_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_discr_1328_ = l_Lean_Syntax_getArg(v_stx_1304_, v___x_1327_);
                    v___x_1329_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_alts_1330_ = l_Lean_Syntax_getArg(v_stx_1304_, v___x_1329_);
                    crate::leanh::lean_dec(v_stx_1304_);
                    if crate::leanh::lean_obj_tag(v_metaFalseTk_x3f_1317_) == 0 {
                        if v___x_1315_ == 0 {
                            v___x_1331_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_a_1326_, v_discr_1328_, v_alts_1330_, v_dec_1305_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
                            return v___x_1331_;
                        } else {
                            v___x_1332_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__1;
                            v___x_1333_ =
                                l_Lean_Core_mkFreshUserName(v___x_1332_, v___y_1323_, v___y_1324_);
                            if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
                                v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                                crate::leanh::lean_inc(v_a_1334_);
                                crate::leanh::lean_dec_ref_known(v___x_1333_, 1);
                                v_ref_1335_ = crate::leanh::lean_ctor_get(v___y_1323_, 5);
                                v_quotContext_1336_ = crate::leanh::lean_ctor_get(v___y_1323_, 10);
                                v_currMacroScope_1337_ =
                                    crate::leanh::lean_ctor_get(v___y_1323_, 11);
                                v___x_1338_ = 0;
                                v___x_1339_ =
                                    l_Lean_mkIdentFrom(v_discr_1328_, v_a_1334_, v___x_1338_);
                                v___x_1340_ = l_Lean_SourceInfo_fromRef(v_ref_1335_, v___x_1338_);
                                v___x_1341_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__3;
                                v___x_1342_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__5;
                                v___x_1343_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7_once), _init_l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__7);
                                v___x_1344_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__8;
                                crate::leanh::lean_inc(v_currMacroScope_1337_);
                                crate::leanh::lean_inc(v_quotContext_1336_);
                                v___x_1345_ = l_Lean_addMacroScope(
                                    v_quotContext_1336_,
                                    v___x_1344_,
                                    v_currMacroScope_1337_,
                                );
                                v___x_1346_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___closed__12;
                                crate::leanh::lean_inc_n(v___x_1340_, 3);
                                v___x_1347_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1347_, 0, v___x_1340_);
                                crate::leanh::lean_ctor_set(v___x_1347_, 1, v___x_1343_);
                                crate::leanh::lean_ctor_set(v___x_1347_, 2, v___x_1345_);
                                crate::leanh::lean_ctor_set(v___x_1347_, 3, v___x_1346_);
                                v___x_1348_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__11;
                                v___x_1349_ =
                                    l_Lean_Syntax_node1(v___x_1340_, v___x_1348_, v_discr_1328_);
                                v___x_1350_ = l_Lean_Syntax_node2(
                                    v___x_1340_,
                                    v___x_1342_,
                                    v___x_1347_,
                                    v___x_1349_,
                                );
                                v___x_1351_ =
                                    l_Lean_Syntax_node1(v___x_1340_, v___x_1341_, v___x_1350_);
                                v___x_1352_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc(v___x_1339_);
                                v___x_1353_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta___boxed as *mut core::ffi::c_void, 12, 4);
                                crate::leanh::lean_closure_set(v___x_1353_, 0, v_a_1326_);
                                crate::leanh::lean_closure_set(v___x_1353_, 1, v___x_1339_);
                                crate::leanh::lean_closure_set(v___x_1353_, 2, v_alts_1330_);
                                crate::leanh::lean_closure_set(v___x_1353_, 3, v_dec_1305_);
                                v___x_1354_ = 0;
                                v___x_1355_ = l_Lean_Elab_Do_elabDoIdDecl(
                                    v___x_1339_,
                                    v___x_1352_,
                                    v___x_1351_,
                                    v___x_1353_,
                                    v___x_1354_,
                                    v___y_1318_,
                                    v___y_1319_,
                                    v___y_1320_,
                                    v___y_1321_,
                                    v___y_1322_,
                                    v___y_1323_,
                                    v___y_1324_,
                                );
                                return v___x_1355_;
                            } else {
                                crate::leanh::lean_dec(v_alts_1330_);
                                crate::leanh::lean_dec(v_discr_1328_);
                                crate::leanh::lean_dec(v_a_1326_);
                                crate::leanh::lean_dec_ref(v_dec_1305_);
                                v_a_1356_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                                v_isSharedCheck_1363_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                                if v_isSharedCheck_1363_ == 0 {
                                    v___x_1358_ = v___x_1333_;
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1356_);
                                    crate::leanh::lean_dec(v___x_1333_);
                                    v___x_1358_ = crate::leanh::lean_box(0);
                                    v_isShared_1359_ = v_isSharedCheck_1363_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_metaFalseTk_x3f_1317_, 1);
                        v___x_1364_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr_elabDoMatchExprNoMeta(v_a_1326_, v_discr_1328_, v_alts_1330_, v_dec_1305_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
                        return v___x_1364_;
                    }
                } else {
                    crate::leanh::lean_dec(v_metaFalseTk_x3f_1317_);
                    crate::leanh::lean_dec_ref(v_dec_1305_);
                    crate::leanh::lean_dec(v_stx_1304_);
                    v_a_1365_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1372_ = (!crate::leanh::lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1372_ == 0 {
                        v___x_1367_ = v___x_1325_;
                        v_isShared_1368_ = v_isSharedCheck_1372_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1365_);
                        crate::leanh::lean_dec(v___x_1325_);
                        v___x_1367_ = crate::leanh::lean_box(0);
                        v_isShared_1368_ = v_isSharedCheck_1372_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1359_ == 0 {
                    v___x_1361_ = v___x_1358_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
                    v___x_1361_ = v_reuseFailAlloc_1362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1361_;
            }
            4 => {
                if v_isShared_1368_ == 0 {
                    v___x_1370_ = v___x_1367_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed(
    mut v_stx_1384_: *mut crate::leanh::LeanObject,
    mut v_dec_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
    mut v_a_1388_: *mut crate::leanh::LeanObject,
    mut v_a_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1394_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr(
        v_stx_1384_,
        v_dec_1385_,
        v_a_1386_,
        v_a_1387_,
        v_a_1388_,
        v_a_1389_,
        v_a_1390_,
        v_a_1391_,
        v_a_1392_,
    );
    crate::leanh::lean_dec(v_a_1392_);
    crate::leanh::lean_dec_ref(v_a_1391_);
    crate::leanh::lean_dec(v_a_1390_);
    crate::leanh::lean_dec_ref(v_a_1389_);
    crate::leanh::lean_dec(v_a_1388_);
    crate::leanh::lean_dec_ref(v_a_1387_);
    crate::leanh::lean_dec_ref(v_a_1386_);
    return v_res_1394_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_1401_ =
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___closed__8;
    v___x_1402_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___closed__1;
    v___x_1403_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1404_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1400_,
        v___x_1401_,
        v___x_1402_,
        v___x_1403_,
    );
    return v___x_1404_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1___boxed(
    mut v_a_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1406_ = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
    return v_res_1406_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetExpr__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_expandDoLetMetaExpr__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr___regBuiltin___private_Lean_Elab_BuiltinDo_MatchExpr_0__Lean_Elab_Do_elabDoMatchExpr__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_MatchExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_MatchExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_PatternVar(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_MatchExpr(builtin);
}
