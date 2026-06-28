// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Syntax
// Imports: Lean.Elab.BuiltinNotation Std.Do.Triple.Basic
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::lean_mk_syntax_ident;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::BuiltinNotation::{
    initialize_Lean_Elab_BuiltinNotation, runtime_initialize_Lean_Elab_BuiltinNotation,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_termElabAttribute,
    l_Lean_Elab_Term_tryPostponeIfMVar,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_consumeMData,
    l_Lean_Expr_hasMVar, l_Lean_mkApp7, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_Level_dec;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkFreshExprMVar;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::Delaborator::Basic::{
    l_Lean_PrettyPrinter_Delaborator_delab___boxed, l_Lean_PrettyPrinter_Delaborator_delabAttribute,
};
use crate::r#gen::Lean::SubExpr::l_Lean_SubExpr_Pos_push;
use crate::r#gen::Std::Do::Triple::Basic::{
    initialize_Std_Do_Triple_Basic, runtime_initialize_Std_Do_Triple_Basic,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject,13979102795498516556 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject,7932075773091973500 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut crate::leanh::LeanObject,14296711813398647265 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut crate::leanh::LeanObject,7043493786777132025 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut crate::leanh::LeanObject,5346268661279150583 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut crate::leanh::LeanObject,7306243862518720553 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut crate::leanh::LeanObject,13332341187416043682 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut crate::leanh::LeanObject,611622866940524098 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut crate::leanh::LeanObject,300274991653824376 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut crate::leanh::LeanObject,18105168627502861736 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut crate::leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut crate::leanh::LeanObject,16077784126176397009 as *mut crate::leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value) as *mut crate::leanh::LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value) as *mut crate::leanh::LeanObject,12966880221525079621 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut crate::leanh::LeanObject,3393990892394863740 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut crate::leanh::LeanObject,11553573755926099728 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 10, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value) as *mut crate::leanh::LeanObject,8463861479368259073 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value) as *mut crate::leanh::LeanObject,2214559063752339918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 135, 147, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut crate::leanh::LeanObject,13156709450692335107 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut crate::leanh::LeanObject,3676176009791887579 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,14659826576719934041 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut crate::leanh::LeanObject,6004524207281992990 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9130596894474051559 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7722122208264906652 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,14847410795624973596 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 78, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut crate::leanh::LeanObject,17122680503757600671 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut crate::leanh::LeanObject,3393990892394863740 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut crate::leanh::LeanObject,2940964116523157683 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 11, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 63, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value) as *mut crate::leanh::LeanObject,5101830612129297492 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 135, 147, 63, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut crate::leanh::LeanObject,13156709450692335107 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut crate::leanh::LeanObject,7425120582457359416 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 77, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut crate::leanh::LeanObject,4163951709596513047 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value) as *mut crate::leanh::LeanObject,13939969460734853986 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 114, 101, 100, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value) as *mut crate::leanh::LeanObject,4155561471746556359 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut crate::leanh::LeanObject,3393990892394863740 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value) as *mut crate::leanh::LeanObject,11963640885769744415 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value) as *mut crate::leanh::LeanObject,6471916472876379905 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 80, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,7300584325018775040 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value) as *mut crate::leanh::LeanObject,6757038018435374033 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [87, 114, 111, 110, 103, 32, 108, 101, 118, 101, 108, 32, 48, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 121, 112, 101, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 121, 112, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut crate::leanh::LeanObject,4122983324971754373 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20;
    v___x_1248_ = l_String_toRawSubstring_x27(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1305_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_P_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v_ref_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v_ref_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v_ref_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1432_: u8 = 0;
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_P_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v_ref_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1313_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3;
                crate::leanh::lean_inc(v_x_1310_);
                v___x_1314_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1313_);
                if v___x_1314_ == 0 {
                    v___x_1315_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8;
                    crate::leanh::lean_inc(v_x_1310_);
                    v___x_1316_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1315_);
                    if v___x_1316_ == 0 {
                        v___x_1317_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10;
                        crate::leanh::lean_inc(v_x_1310_);
                        v___x_1318_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1317_);
                        if v___x_1318_ == 0 {
                            v___x_1319_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11;
                            v___x_1320_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12;
                            crate::leanh::lean_inc(v_x_1310_);
                            v___x_1321_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1320_);
                            if v___x_1321_ == 0 {
                                v___x_1322_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14;
                                crate::leanh::lean_inc(v_x_1310_);
                                v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1322_);
                                if v___x_1323_ == 0 {
                                    v___x_1324_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1324_, 0, v_x_1310_);
                                    return v___x_1324_;
                                } else {
                                    v___x_1325_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_1326_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1325_);
                                    v___x_1327_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                                    crate::leanh::lean_inc(v___x_1326_);
                                    v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
                                    if v___x_1328_ == 0 {
                                        crate::leanh::lean_dec(v___x_1326_);
                                        v___x_1329_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1329_, 0, v_x_1310_);
                                        return v___x_1329_;
                                    } else {
                                        v___x_1330_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v___x_1331_ =
                                            l_Lean_Syntax_getArg(v___x_1326_, v___x_1330_);
                                        crate::leanh::lean_dec(v___x_1326_);
                                        v___x_1332_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                                        crate::leanh::lean_inc(v___x_1331_);
                                        v___x_1333_ =
                                            l_Lean_Syntax_isOfKind(v___x_1331_, v___x_1332_);
                                        if v___x_1333_ == 0 {
                                            crate::leanh::lean_dec(v___x_1331_);
                                            v___x_1334_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(v___x_1334_, 0, v_x_1310_);
                                            return v___x_1334_;
                                        } else {
                                            v___x_1335_ =
                                                l_Lean_Syntax_getArg(v___x_1331_, v___x_1325_);
                                            crate::leanh::lean_dec(v___x_1331_);
                                            v___x_1336_ = crate::leanh::lean_box(0);
                                            v___x_1337_ = l_Lean_Syntax_matchesIdent(
                                                v___x_1335_,
                                                v___x_1336_,
                                            );
                                            crate::leanh::lean_dec(v___x_1335_);
                                            if v___x_1337_ == 0 {
                                                v___x_1338_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_1338_,
                                                    0,
                                                    v_x_1310_,
                                                );
                                                return v___x_1338_;
                                            } else {
                                                v___x_1339_ = crate::leanh::lean_unsigned_to_nat(3);
                                                v___x_1340_ =
                                                    l_Lean_Syntax_getArg(v_x_1310_, v___x_1339_);
                                                crate::leanh::lean_inc(v___x_1340_);
                                                v___x_1341_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1340_,
                                                    v___x_1330_,
                                                );
                                                if v___x_1341_ == 0 {
                                                    crate::leanh::lean_dec(v___x_1340_);
                                                    v___x_1342_ = crate::leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_1342_,
                                                        0,
                                                        v_x_1310_,
                                                    );
                                                    return v___x_1342_;
                                                } else {
                                                    v_P_1343_ = l_Lean_Syntax_getArg(
                                                        v_x_1310_,
                                                        v___x_1330_,
                                                    );
                                                    crate::leanh::lean_dec(v_x_1310_);
                                                    v___x_1344_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1343_, v___y_1311_);
                                                    if crate::leanh::lean_obj_tag(v___x_1344_) == 0
                                                    {
                                                        v_a_1345_ = crate::leanh::lean_ctor_get(
                                                            v___x_1344_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1372_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_1344_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_1372_ == 0 {
                                                            v___x_1347_ = v___x_1344_;
                                                            v_isShared_1348_ =
                                                                v_isSharedCheck_1372_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_1345_);
                                                            crate::leanh::lean_dec(v___x_1344_);
                                                            v___x_1347_ = crate::leanh::lean_box(0);
                                                            v_isShared_1348_ =
                                                                v_isSharedCheck_1372_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_1340_);
                                                        return v___x_1344_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_1373_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1374_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1373_);
                                v___x_1375_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                                crate::leanh::lean_inc(v___x_1374_);
                                v___x_1376_ = l_Lean_Syntax_isOfKind(v___x_1374_, v___x_1375_);
                                if v___x_1376_ == 0 {
                                    crate::leanh::lean_dec(v___x_1374_);
                                    v___x_1377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1377_, 0, v_x_1310_);
                                    return v___x_1377_;
                                } else {
                                    v___x_1378_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1373_);
                                    v___x_1380_ =
                                        l_Lean_Syntax_matchesNull(v___x_1379_, v___x_1378_);
                                    if v___x_1380_ == 0 {
                                        crate::leanh::lean_dec(v___x_1374_);
                                        v___x_1381_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1381_, 0, v_x_1310_);
                                        return v___x_1381_;
                                    } else {
                                        crate::leanh::lean_dec(v_x_1310_);
                                        v___x_1382_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v_b_1383_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1382_);
                                        v___x_1384_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_b_1383_, v___y_1311_);
                                        if crate::leanh::lean_obj_tag(v___x_1384_) == 0 {
                                            v_a_1385_ = crate::leanh::lean_ctor_get(v___x_1384_, 0);
                                            v_isSharedCheck_1406_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_1384_))
                                                    as u8;
                                            if v_isSharedCheck_1406_ == 0 {
                                                v___x_1387_ = v___x_1384_;
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_1385_);
                                                crate::leanh::lean_dec(v___x_1384_);
                                                v___x_1387_ = crate::leanh::lean_box(0);
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_1374_);
                                            return v___x_1384_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_1407_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_t_1408_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1407_);
                            v___x_1409_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_t_1408_, v___y_1311_);
                            if crate::leanh::lean_obj_tag(v___x_1409_) == 0 {
                                v_a_1410_ = crate::leanh::lean_ctor_get(v___x_1409_, 0);
                                crate::leanh::lean_inc(v_a_1410_);
                                crate::leanh::lean_dec_ref_known(v___x_1409_, 1);
                                v___x_1411_ = crate::leanh::lean_unsigned_to_nat(5);
                                v_e_1412_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1411_);
                                v___x_1413_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_e_1412_, v___y_1311_);
                                if crate::leanh::lean_obj_tag(v___x_1413_) == 0 {
                                    v_a_1414_ = crate::leanh::lean_ctor_get(v___x_1413_, 0);
                                    v_isSharedCheck_1432_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1413_)) as u8;
                                    if v_isSharedCheck_1432_ == 0 {
                                        v___x_1416_ = v___x_1413_;
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1414_);
                                        crate::leanh::lean_dec(v___x_1413_);
                                        v___x_1416_ = crate::leanh::lean_box(0);
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1410_);
                                    crate::leanh::lean_dec(v_x_1310_);
                                    return v___x_1413_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_x_1310_);
                                return v___x_1409_;
                            }
                        }
                    } else {
                        v___x_1433_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1434_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1433_);
                        v___x_1435_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                        crate::leanh::lean_inc(v___x_1434_);
                        v___x_1436_ = l_Lean_Syntax_isOfKind(v___x_1434_, v___x_1435_);
                        if v___x_1436_ == 0 {
                            crate::leanh::lean_dec(v___x_1434_);
                            v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1437_, 0, v_x_1310_);
                            return v___x_1437_;
                        } else {
                            v___x_1438_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1439_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1438_);
                            crate::leanh::lean_dec(v___x_1434_);
                            v___x_1440_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                            crate::leanh::lean_inc(v___x_1439_);
                            v___x_1441_ = l_Lean_Syntax_isOfKind(v___x_1439_, v___x_1440_);
                            if v___x_1441_ == 0 {
                                crate::leanh::lean_dec(v___x_1439_);
                                v___x_1442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1442_, 0, v_x_1310_);
                                return v___x_1442_;
                            } else {
                                v___x_1443_ = l_Lean_Syntax_getArg(v___x_1439_, v___x_1433_);
                                crate::leanh::lean_dec(v___x_1439_);
                                v___x_1444_ = crate::leanh::lean_box(0);
                                v___x_1445_ = l_Lean_Syntax_matchesIdent(v___x_1443_, v___x_1444_);
                                crate::leanh::lean_dec(v___x_1443_);
                                if v___x_1445_ == 0 {
                                    v___x_1446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1446_, 0, v_x_1310_);
                                    return v___x_1446_;
                                } else {
                                    v_P_1447_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1438_);
                                    crate::leanh::lean_dec(v_x_1310_);
                                    v___x_1448_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1447_, v___y_1311_);
                                    if crate::leanh::lean_obj_tag(v___x_1448_) == 0 {
                                        v_a_1449_ = crate::leanh::lean_ctor_get(v___x_1448_, 0);
                                        v_isSharedCheck_1471_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1448_)) as u8;
                                        if v_isSharedCheck_1471_ == 0 {
                                            v___x_1451_ = v___x_1448_;
                                            v_isShared_1452_ = v_isSharedCheck_1471_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1449_);
                                            crate::leanh::lean_dec(v___x_1448_);
                                            v___x_1451_ = crate::leanh::lean_box(0);
                                            v_isShared_1452_ = v_isSharedCheck_1471_;
                                            state = 7;
                                            continue;
                                        }
                                    } else {
                                        return v___x_1448_;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_1472_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1473_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1472_);
                    crate::leanh::lean_dec(v_x_1310_);
                    v___x_1474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                    return v___x_1474_;
                }
            }
            1 => {
                v_ref_1349_ = crate::leanh::lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1350_ = crate::leanh::lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1351_ = crate::leanh::lean_ctor_get(v___y_1311_, 11);
                v___x_1352_ = l_Lean_Syntax_getArg(v___x_1340_, v___x_1325_);
                crate::leanh::lean_dec(v___x_1340_);
                v___x_1353_ = l_Lean_SourceInfo_fromRef(v_ref_1349_, v___x_1321_);
                v___x_1354_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                crate::leanh::lean_inc_n(v___x_1353_, 7);
                v___x_1355_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1355_, 0, v___x_1353_);
                crate::leanh::lean_ctor_set(v___x_1355_, 1, v___x_1354_);
                v___x_1356_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                crate::leanh::lean_inc(v_currMacroScope_1351_);
                crate::leanh::lean_inc(v_quotContext_1350_);
                v___x_1357_ =
                    l_Lean_addMacroScope(v_quotContext_1350_, v___x_1336_, v_currMacroScope_1351_);
                v___x_1358_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1359_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1353_);
                crate::leanh::lean_ctor_set(v___x_1359_, 1, v___x_1356_);
                crate::leanh::lean_ctor_set(v___x_1359_, 2, v___x_1357_);
                crate::leanh::lean_ctor_set(v___x_1359_, 3, v___x_1358_);
                v___x_1360_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1332_, v___x_1359_);
                v___x_1361_ =
                    l_Lean_Syntax_node2(v___x_1353_, v___x_1327_, v___x_1355_, v___x_1360_);
                v___x_1362_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41;
                v___x_1363_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1363_, 0, v___x_1353_);
                crate::leanh::lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                v___x_1364_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1365_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1364_, v___x_1352_);
                v___x_1366_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1367_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1367_, 0, v___x_1353_);
                crate::leanh::lean_ctor_set(v___x_1367_, 1, v___x_1366_);
                v___x_1368_ = l_Lean_Syntax_node5(
                    v___x_1353_,
                    v___x_1322_,
                    v___x_1361_,
                    v_a_1345_,
                    v___x_1363_,
                    v___x_1365_,
                    v___x_1367_,
                );
                if v_isShared_1348_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1347_, 0, v___x_1368_);
                    v___x_1370_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1370_;
            }
            3 => {
                v_ref_1389_ = crate::leanh::lean_ctor_get(v___y_1311_, 5);
                v___x_1390_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1378_);
                crate::leanh::lean_dec(v___x_1374_);
                v_xs_1391_ = l_Lean_Syntax_getArgs(v___x_1390_);
                crate::leanh::lean_dec(v___x_1390_);
                v___x_1392_ = l_Lean_SourceInfo_fromRef(v_ref_1389_, v___x_1318_);
                crate::leanh::lean_inc_n(v___x_1392_, 5);
                v___x_1393_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1393_, 0, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1393_, 1, v___x_1319_);
                v___x_1394_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1395_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                v___x_1396_ = l_Array_append___redArg(v___x_1395_, v_xs_1391_);
                crate::leanh::lean_dec_ref(v_xs_1391_);
                v___x_1397_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1397_, 0, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1397_, 1, v___x_1394_);
                crate::leanh::lean_ctor_set(v___x_1397_, 2, v___x_1396_);
                v___x_1398_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1398_, 0, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1398_, 1, v___x_1394_);
                crate::leanh::lean_ctor_set(v___x_1398_, 2, v___x_1395_);
                v___x_1399_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1400_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1392_);
                crate::leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
                v___x_1401_ = l_Lean_Syntax_node4(
                    v___x_1392_,
                    v___x_1375_,
                    v___x_1397_,
                    v___x_1398_,
                    v___x_1400_,
                    v_a_1385_,
                );
                v___x_1402_ =
                    l_Lean_Syntax_node2(v___x_1392_, v___x_1320_, v___x_1393_, v___x_1401_);
                if v_isShared_1388_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1387_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1404_;
            }
            5 => {
                v_ref_1418_ = crate::leanh::lean_ctor_get(v___y_1311_, 5);
                v___x_1419_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1420_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1419_);
                crate::leanh::lean_dec(v_x_1310_);
                v___x_1421_ = l_Lean_SourceInfo_fromRef(v_ref_1418_, v___x_1316_);
                v___x_1422_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49;
                crate::leanh::lean_inc_n(v___x_1421_, 3);
                v___x_1423_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1423_, 0, v___x_1421_);
                crate::leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
                v___x_1424_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50;
                v___x_1425_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1425_, 0, v___x_1421_);
                crate::leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
                v___x_1426_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51;
                v___x_1427_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1427_, 0, v___x_1421_);
                crate::leanh::lean_ctor_set(v___x_1427_, 1, v___x_1426_);
                v___x_1428_ = l_Lean_Syntax_node6(
                    v___x_1421_,
                    v___x_1317_,
                    v___x_1423_,
                    v___x_1420_,
                    v___x_1425_,
                    v_a_1410_,
                    v___x_1427_,
                    v_a_1414_,
                );
                if v_isShared_1417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1416_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1430_;
            }
            7 => {
                v_ref_1453_ = crate::leanh::lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1454_ = crate::leanh::lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1455_ = crate::leanh::lean_ctor_get(v___y_1311_, 11);
                v___x_1456_ = l_Lean_SourceInfo_fromRef(v_ref_1453_, v___x_1314_);
                v___x_1457_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                crate::leanh::lean_inc_n(v___x_1456_, 5);
                v___x_1458_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1458_, 0, v___x_1456_);
                crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                v___x_1459_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                crate::leanh::lean_inc(v_currMacroScope_1455_);
                crate::leanh::lean_inc(v_quotContext_1454_);
                v___x_1460_ =
                    l_Lean_addMacroScope(v_quotContext_1454_, v___x_1444_, v_currMacroScope_1455_);
                v___x_1461_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1462_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1456_);
                crate::leanh::lean_ctor_set(v___x_1462_, 1, v___x_1459_);
                crate::leanh::lean_ctor_set(v___x_1462_, 2, v___x_1460_);
                crate::leanh::lean_ctor_set(v___x_1462_, 3, v___x_1461_);
                v___x_1463_ = l_Lean_Syntax_node1(v___x_1456_, v___x_1440_, v___x_1462_);
                v___x_1464_ =
                    l_Lean_Syntax_node2(v___x_1456_, v___x_1435_, v___x_1458_, v___x_1463_);
                v___x_1465_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1466_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1466_, 0, v___x_1456_);
                crate::leanh::lean_ctor_set(v___x_1466_, 1, v___x_1465_);
                v___x_1467_ = l_Lean_Syntax_node3(
                    v___x_1456_,
                    v___x_1315_,
                    v___x_1464_,
                    v_a_1449_,
                    v___x_1466_,
                );
                if v_isShared_1452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1451_, 0, v___x_1467_);
                    v___x_1469_ = v___x_1451_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
                    v___x_1469_ = v_reuseFailAlloc_1470_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___boxed(
    mut v_x_1475_: *mut crate::leanh::LeanObject,
    mut v___y_1476_: *mut crate::leanh::LeanObject,
    mut v___y_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1475_, v___y_1476_);
    crate::leanh::lean_dec_ref(v___y_1476_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(
    mut v_child_1479_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1480_: *mut crate::leanh::LeanObject,
    mut v_x_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
    mut v___y_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subExpr_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionsPerPos_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inPattern_1493_: u8 = 0;
    let mut v_depth_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctxInitIndices_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subExpr_1489_ = crate::leanh::lean_ctor_get(v___y_1482_, 3);
    v_optionsPerPos_1490_ = crate::leanh::lean_ctor_get(v___y_1482_, 0);
    v_currNamespace_1491_ = crate::leanh::lean_ctor_get(v___y_1482_, 1);
    v_openDecls_1492_ = crate::leanh::lean_ctor_get(v___y_1482_, 2);
    v_inPattern_1493_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1482_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
    );
    v_depth_1494_ = crate::leanh::lean_ctor_get(v___y_1482_, 4);
    v_lctxInitIndices_1495_ = crate::leanh::lean_ctor_get(v___y_1482_, 5);
    v_pos_1496_ = crate::leanh::lean_ctor_get(v_subExpr_1489_, 1);
    v___x_1497_ = l_Lean_SubExpr_Pos_push(v_pos_1496_, v_childIdx_1480_);
    v___x_1498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1498_, 0, v_child_1479_);
    crate::leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    crate::leanh::lean_inc(v_lctxInitIndices_1495_);
    crate::leanh::lean_inc(v_depth_1494_);
    crate::leanh::lean_inc(v_openDecls_1492_);
    crate::leanh::lean_inc(v_currNamespace_1491_);
    crate::leanh::lean_inc(v_optionsPerPos_1490_);
    v___x_1499_ = crate::leanh::lean_alloc_ctor(0, 6, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1499_, 0, v_optionsPerPos_1490_);
    crate::leanh::lean_ctor_set(v___x_1499_, 1, v_currNamespace_1491_);
    crate::leanh::lean_ctor_set(v___x_1499_, 2, v_openDecls_1492_);
    crate::leanh::lean_ctor_set(v___x_1499_, 3, v___x_1498_);
    crate::leanh::lean_ctor_set(v___x_1499_, 4, v_depth_1494_);
    crate::leanh::lean_ctor_set(v___x_1499_, 5, v_lctxInitIndices_1495_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1499_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
        v_inPattern_1493_,
    );
    crate::leanh::lean_inc(v___y_1487_);
    crate::leanh::lean_inc_ref(v___y_1486_);
    crate::leanh::lean_inc(v___y_1485_);
    crate::leanh::lean_inc_ref(v___y_1484_);
    crate::leanh::lean_inc(v___y_1483_);
    v___x_1500_ = crate::leanh::lean_apply_7(
        v_x_1481_,
        v___x_1499_,
        v___y_1483_,
        v___y_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
        crate::leanh::lean_box(0),
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(
    mut v_child_1501_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1502_: *mut crate::leanh::LeanObject,
    mut v_x_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1501_, v_childIdx_1502_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
    crate::leanh::lean_dec(v___y_1509_);
    crate::leanh::lean_dec_ref(v___y_1508_);
    crate::leanh::lean_dec(v___y_1507_);
    crate::leanh::lean_dec_ref(v___y_1506_);
    crate::leanh::lean_dec(v___y_1505_);
    crate::leanh::lean_dec_ref(v___y_1504_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(
    mut v___y_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subExpr_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subExpr_1514_ = crate::leanh::lean_ctor_get(v___y_1512_, 3);
    v_expr_1515_ = crate::leanh::lean_ctor_get(v_subExpr_1514_, 0);
    crate::leanh::lean_inc_ref(v_expr_1515_);
    v___x_1516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1516_, 0, v_expr_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1517_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    return v_res_1519_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(
    mut v_x_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
    mut v___y_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1521_);
    v_a_1529_ = crate::leanh::lean_ctor_get(v___x_1528_, 0);
    crate::leanh::lean_inc(v_a_1529_);
    crate::leanh::lean_dec_ref(v___x_1528_);
    v___x_1530_ = l_Lean_Expr_appArg_x21(v_a_1529_);
    crate::leanh::lean_dec(v_a_1529_);
    v___x_1531_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1532_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v___x_1530_, v___x_1531_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(
    mut v_x_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
    mut v___y_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
    crate::leanh::lean_dec(v___y_1539_);
    crate::leanh::lean_dec_ref(v___y_1538_);
    crate::leanh::lean_dec(v___y_1537_);
    crate::leanh::lean_dec_ref(v___y_1536_);
    crate::leanh::lean_dec(v___y_1535_);
    crate::leanh::lean_dec_ref(v___y_1534_);
    return v_res_1541_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5;
    v___x_1557_ = lean_mk_syntax_ident(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v_ref_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v_ref_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_ref_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v_ref_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1574_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1575_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1574_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
                if crate::leanh::lean_obj_tag(v___x_1575_) == 0 {
                    v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1575_, 0);
                    v_isSharedCheck_1647_ = (!crate::leanh::lean_is_exclusive(v___x_1575_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1578_ = v___x_1575_;
                        v_isShared_1579_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1576_);
                        crate::leanh::lean_dec(v___x_1575_);
                        v___x_1578_ = crate::leanh::lean_box(0);
                        v_isShared_1579_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1575_;
                }
            }
            1 => {
                v___x_1580_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12;
                crate::leanh::lean_inc(v_a_1576_);
                v___x_1581_ = l_Lean_Syntax_isOfKind(v_a_1576_, v___x_1580_);
                if v___x_1581_ == 0 {
                    v_ref_1582_ = crate::leanh::lean_ctor_get(v_a_1571_, 5);
                    v___x_1583_ = l_Lean_SourceInfo_fromRef(v_ref_1582_, v___x_1581_);
                    v___x_1584_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                    v___x_1586_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    crate::leanh::lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Syntax_node1(v___x_1583_, v___x_1586_, v_a_1576_);
                    v___x_1588_ =
                        l_Lean_Syntax_node2(v___x_1583_, v___x_1584_, v___x_1585_, v___x_1587_);
                    if v_isShared_1579_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1588_);
                        v___x_1590_ = v___x_1578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
                        v___x_1590_ = v_reuseFailAlloc_1591_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1592_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1593_ = l_Lean_Syntax_getArg(v_a_1576_, v___x_1592_);
                    v___x_1594_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    crate::leanh::lean_inc(v___x_1593_);
                    v___x_1595_ = l_Lean_Syntax_isOfKind(v___x_1593_, v___x_1594_);
                    if v___x_1595_ == 0 {
                        crate::leanh::lean_dec(v___x_1593_);
                        v_ref_1596_ = crate::leanh::lean_ctor_get(v_a_1571_, 5);
                        v___x_1597_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1595_);
                        v___x_1598_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1599_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                        v___x_1600_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        crate::leanh::lean_inc(v___x_1597_);
                        v___x_1601_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1600_, v_a_1576_);
                        v___x_1602_ =
                            l_Lean_Syntax_node2(v___x_1597_, v___x_1598_, v___x_1599_, v___x_1601_);
                        if v_isShared_1579_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1602_);
                            v___x_1604_ = v___x_1578_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1605_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                            v___x_1604_ = v_reuseFailAlloc_1605_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1606_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1607_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1592_);
                        v___x_1608_ = l_Lean_Syntax_matchesNull(v___x_1607_, v___x_1606_);
                        if v___x_1608_ == 0 {
                            crate::leanh::lean_dec(v___x_1593_);
                            v_ref_1609_ = crate::leanh::lean_ctor_get(v_a_1571_, 5);
                            v___x_1610_ = l_Lean_SourceInfo_fromRef(v_ref_1609_, v___x_1608_);
                            v___x_1611_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                            v___x_1613_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            crate::leanh::lean_inc(v___x_1610_);
                            v___x_1614_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1613_, v_a_1576_);
                            v___x_1615_ = l_Lean_Syntax_node2(
                                v___x_1610_,
                                v___x_1611_,
                                v___x_1612_,
                                v___x_1614_,
                            );
                            if v_isShared_1579_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1615_);
                                v___x_1617_ = v___x_1578_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1618_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
                                v___x_1617_ = v_reuseFailAlloc_1618_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1578_);
                            crate::leanh::lean_dec(v_a_1576_);
                            v___x_1619_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1620_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1619_);
                            v___x_1621_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1620_, v_a_1571_);
                            if crate::leanh::lean_obj_tag(v___x_1621_) == 0 {
                                v_a_1622_ = crate::leanh::lean_ctor_get(v___x_1621_, 0);
                                v_isSharedCheck_1646_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1621_)) as u8;
                                if v_isSharedCheck_1646_ == 0 {
                                    v___x_1624_ = v___x_1621_;
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1622_);
                                    crate::leanh::lean_dec(v___x_1621_);
                                    v___x_1624_ = crate::leanh::lean_box(0);
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1593_);
                                return v___x_1621_;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1590_;
            }
            3 => {
                return v___x_1604_;
            }
            4 => {
                return v___x_1617_;
            }
            5 => {
                v_ref_1626_ = crate::leanh::lean_ctor_get(v_a_1571_, 5);
                v___x_1627_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1606_);
                crate::leanh::lean_dec(v___x_1593_);
                v___x_1628_ = l_Lean_Syntax_getArgs(v___x_1627_);
                crate::leanh::lean_dec(v___x_1627_);
                v___x_1629_ = 0;
                v___x_1630_ = l_Lean_SourceInfo_fromRef(v_ref_1626_, v___x_1629_);
                v___x_1631_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8;
                v___x_1632_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1633_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                crate::leanh::lean_inc_n(v___x_1630_, 4);
                v___x_1634_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1634_, 0, v___x_1630_);
                crate::leanh::lean_ctor_set(v___x_1634_, 1, v___x_1632_);
                crate::leanh::lean_ctor_set(v___x_1634_, 2, v___x_1633_);
                v___x_1635_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11;
                v___x_1636_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1636_, 0, v___x_1630_);
                crate::leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                v___x_1637_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1638_ = l_Array_append___redArg(v___x_1633_, v___x_1628_);
                crate::leanh::lean_dec_ref(v___x_1628_);
                v___x_1639_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1639_, 0, v___x_1630_);
                crate::leanh::lean_ctor_set(v___x_1639_, 1, v___x_1637_);
                crate::leanh::lean_ctor_set(v___x_1639_, 2, v___x_1638_);
                v___x_1640_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1641_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1641_, 0, v___x_1630_);
                crate::leanh::lean_ctor_set(v___x_1641_, 1, v___x_1640_);
                v___x_1642_ = l_Lean_Syntax_node5(
                    v___x_1630_,
                    v___x_1631_,
                    v___x_1634_,
                    v___x_1636_,
                    v___x_1639_,
                    v___x_1641_,
                    v_a_1622_,
                );
                if v_isShared_1625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1642_);
                    v___x_1644_ = v___x_1624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed(
    mut v_a_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
    mut v_a_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
        v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_,
    );
    crate::leanh::lean_dec(v_a_1653_);
    crate::leanh::lean_dec_ref(v_a_1652_);
    crate::leanh::lean_dec(v_a_1651_);
    crate::leanh::lean_dec_ref(v_a_1650_);
    crate::leanh::lean_dec(v_a_1649_);
    crate::leanh::lean_dec_ref(v_a_1648_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1656_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
    crate::leanh::lean_dec(v___y_1669_);
    crate::leanh::lean_dec_ref(v___y_1668_);
    crate::leanh::lean_dec(v___y_1667_);
    crate::leanh::lean_dec_ref(v___y_1666_);
    crate::leanh::lean_dec(v___y_1665_);
    crate::leanh::lean_dec_ref(v___y_1664_);
    return v_res_1671_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(
    mut v_00_u03b1_1672_: *mut crate::leanh::LeanObject,
    mut v_child_1673_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1674_: *mut crate::leanh::LeanObject,
    mut v_x_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1673_, v_childIdx_1674_, v_x_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(
    mut v_00_u03b1_1684_: *mut crate::leanh::LeanObject,
    mut v_child_1685_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1686_: *mut crate::leanh::LeanObject,
    mut v_x_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(v_00_u03b1_1684_, v_child_1685_, v_childIdx_1686_, v_x_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
    crate::leanh::lean_dec(v___y_1693_);
    crate::leanh::lean_dec_ref(v___y_1692_);
    crate::leanh::lean_dec(v___y_1691_);
    crate::leanh::lean_dec_ref(v___y_1690_);
    crate::leanh::lean_dec(v___y_1689_);
    crate::leanh::lean_dec_ref(v___y_1688_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(
    mut v_00_u03b1_1696_: *mut crate::leanh::LeanObject,
    mut v_x_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
    return v___x_1705_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(
    mut v_00_u03b1_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
    mut v___y_1709_: *mut crate::leanh::LeanObject,
    mut v___y_1710_: *mut crate::leanh::LeanObject,
    mut v___y_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(v_00_u03b1_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
    crate::leanh::lean_dec(v___y_1713_);
    crate::leanh::lean_dec_ref(v___y_1712_);
    crate::leanh::lean_dec(v___y_1711_);
    crate::leanh::lean_dec_ref(v___y_1710_);
    crate::leanh::lean_dec(v___y_1709_);
    crate::leanh::lean_dec_ref(v___y_1708_);
    return v_res_1715_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(
    mut v_x_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
    mut v___y_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1716_, v___y_1721_);
    return v___x_1724_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(
    mut v_x_1725_: *mut crate::leanh::LeanObject,
    mut v___y_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    crate::leanh::lean_dec(v___y_1731_);
    crate::leanh::lean_dec_ref(v___y_1730_);
    crate::leanh::lean_dec(v___y_1729_);
    crate::leanh::lean_dec_ref(v___y_1728_);
    crate::leanh::lean_dec(v___y_1727_);
    crate::leanh::lean_dec_ref(v___y_1726_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1774_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0;
    v___x_1775_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15;
    v___x_1776_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___boxed
            as *mut core::ffi::c_void,
        7,
        0,
    );
    v___x_1777_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1773_,
        v___x_1774_,
        v___x_1775_,
        v___x_1776_,
    );
    return v___x_1777_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___boxed(
    mut v_a_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1779_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    return v_res_1779_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1;
    v___x_1787_ = lean_mk_syntax_ident(v___x_1786_);
    return v___x_1787_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
    mut v_a_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v_ref_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v_ref_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v_ref_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v_ref_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1801_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1801_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
                if crate::leanh::lean_obj_tag(v___x_1802_) == 0 {
                    v_a_1803_ = crate::leanh::lean_ctor_get(v___x_1802_, 0);
                    v_isSharedCheck_1874_ = (!crate::leanh::lean_is_exclusive(v___x_1802_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1805_ = v___x_1802_;
                        v_isShared_1806_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1803_);
                        crate::leanh::lean_dec(v___x_1802_);
                        v___x_1805_ = crate::leanh::lean_box(0);
                        v_isShared_1806_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1802_;
                }
            }
            1 => {
                v___x_1807_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12;
                crate::leanh::lean_inc(v_a_1803_);
                v___x_1808_ = l_Lean_Syntax_isOfKind(v_a_1803_, v___x_1807_);
                if v___x_1808_ == 0 {
                    v_ref_1809_ = crate::leanh::lean_ctor_get(v_a_1798_, 5);
                    v___x_1810_ = l_Lean_SourceInfo_fromRef(v_ref_1809_, v___x_1808_);
                    v___x_1811_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                    v___x_1813_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    crate::leanh::lean_inc(v___x_1810_);
                    v___x_1814_ = l_Lean_Syntax_node1(v___x_1810_, v___x_1813_, v_a_1803_);
                    v___x_1815_ =
                        l_Lean_Syntax_node2(v___x_1810_, v___x_1811_, v___x_1812_, v___x_1814_);
                    if v_isShared_1806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1815_);
                        v___x_1817_ = v___x_1805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
                        v___x_1817_ = v_reuseFailAlloc_1818_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1819_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1820_ = l_Lean_Syntax_getArg(v_a_1803_, v___x_1819_);
                    v___x_1821_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    crate::leanh::lean_inc(v___x_1820_);
                    v___x_1822_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1821_);
                    if v___x_1822_ == 0 {
                        crate::leanh::lean_dec(v___x_1820_);
                        v_ref_1823_ = crate::leanh::lean_ctor_get(v_a_1798_, 5);
                        v___x_1824_ = l_Lean_SourceInfo_fromRef(v_ref_1823_, v___x_1822_);
                        v___x_1825_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1826_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                        v___x_1827_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        crate::leanh::lean_inc(v___x_1824_);
                        v___x_1828_ = l_Lean_Syntax_node1(v___x_1824_, v___x_1827_, v_a_1803_);
                        v___x_1829_ =
                            l_Lean_Syntax_node2(v___x_1824_, v___x_1825_, v___x_1826_, v___x_1828_);
                        if v_isShared_1806_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1829_);
                            v___x_1831_ = v___x_1805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1832_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                            v___x_1831_ = v_reuseFailAlloc_1832_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1833_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1834_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1819_);
                        v___x_1835_ = l_Lean_Syntax_matchesNull(v___x_1834_, v___x_1833_);
                        if v___x_1835_ == 0 {
                            crate::leanh::lean_dec(v___x_1820_);
                            v_ref_1836_ = crate::leanh::lean_ctor_get(v_a_1798_, 5);
                            v___x_1837_ = l_Lean_SourceInfo_fromRef(v_ref_1836_, v___x_1835_);
                            v___x_1838_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1839_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                            v___x_1840_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            crate::leanh::lean_inc(v___x_1837_);
                            v___x_1841_ = l_Lean_Syntax_node1(v___x_1837_, v___x_1840_, v_a_1803_);
                            v___x_1842_ = l_Lean_Syntax_node2(
                                v___x_1837_,
                                v___x_1838_,
                                v___x_1839_,
                                v___x_1841_,
                            );
                            if v_isShared_1806_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1842_);
                                v___x_1844_ = v___x_1805_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1845_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
                                v___x_1844_ = v_reuseFailAlloc_1845_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1805_);
                            crate::leanh::lean_dec(v_a_1803_);
                            v___x_1846_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1847_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1846_);
                            v___x_1848_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1847_, v_a_1798_);
                            if crate::leanh::lean_obj_tag(v___x_1848_) == 0 {
                                v_a_1849_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                                v_isSharedCheck_1873_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1848_)) as u8;
                                if v_isSharedCheck_1873_ == 0 {
                                    v___x_1851_ = v___x_1848_;
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1849_);
                                    crate::leanh::lean_dec(v___x_1848_);
                                    v___x_1851_ = crate::leanh::lean_box(0);
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_1820_);
                                return v___x_1848_;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1817_;
            }
            3 => {
                return v___x_1831_;
            }
            4 => {
                return v___x_1844_;
            }
            5 => {
                v_ref_1853_ = crate::leanh::lean_ctor_get(v_a_1798_, 5);
                v___x_1854_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1833_);
                crate::leanh::lean_dec(v___x_1820_);
                v___x_1855_ = l_Lean_Syntax_getArgs(v___x_1854_);
                crate::leanh::lean_dec(v___x_1854_);
                v___x_1856_ = 0;
                v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1856_);
                v___x_1858_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4;
                v___x_1859_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1860_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                crate::leanh::lean_inc_n(v___x_1857_, 4);
                v___x_1861_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1861_, 0, v___x_1857_);
                crate::leanh::lean_ctor_set(v___x_1861_, 1, v___x_1859_);
                crate::leanh::lean_ctor_set(v___x_1861_, 2, v___x_1860_);
                v___x_1862_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5;
                v___x_1863_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v___x_1857_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1865_ = l_Array_append___redArg(v___x_1860_, v___x_1855_);
                crate::leanh::lean_dec_ref(v___x_1855_);
                v___x_1866_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1857_);
                crate::leanh::lean_ctor_set(v___x_1866_, 1, v___x_1864_);
                crate::leanh::lean_ctor_set(v___x_1866_, 2, v___x_1865_);
                v___x_1867_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1868_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1868_, 0, v___x_1857_);
                crate::leanh::lean_ctor_set(v___x_1868_, 1, v___x_1867_);
                v___x_1869_ = l_Lean_Syntax_node5(
                    v___x_1857_,
                    v___x_1858_,
                    v___x_1861_,
                    v___x_1863_,
                    v___x_1866_,
                    v___x_1868_,
                    v_a_1849_,
                );
                if v_isShared_1852_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1851_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1851_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed(
    mut v_a_1875_: *mut crate::leanh::LeanObject,
    mut v_a_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1882_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
        v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_,
    );
    crate::leanh::lean_dec(v_a_1880_);
    crate::leanh::lean_dec_ref(v_a_1879_);
    crate::leanh::lean_dec(v_a_1878_);
    crate::leanh::lean_dec_ref(v_a_1877_);
    crate::leanh::lean_dec(v_a_1876_);
    crate::leanh::lean_dec_ref(v_a_1875_);
    return v_res_1882_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1892_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0;
    v___x_1893_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2;
    v___x_1894_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___boxed
            as *mut core::ffi::c_void,
        7,
        0,
    );
    v___x_1895_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1891_,
        v___x_1892_,
        v___x_1893_,
        v___x_1894_,
    );
    return v___x_1895_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___boxed(
    mut v_a_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    return v_res_1897_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = crate::leanh::lean_box(0);
    v___x_1899_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1900_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0);
    v___x_1903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(
    mut v___y_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v_res_1905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(
    mut v_00_u03b1_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v___x_1914_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(
    mut v_00_u03b1_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(v_00_u03b1_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
    crate::leanh::lean_dec(v___y_1921_);
    crate::leanh::lean_dec_ref(v___y_1920_);
    crate::leanh::lean_dec(v___y_1919_);
    crate::leanh::lean_dec_ref(v___y_1918_);
    crate::leanh::lean_dec(v___y_1917_);
    crate::leanh::lean_dec_ref(v___y_1916_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(
    mut v_e_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_unused_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1927_ = l_Lean_Expr_hasMVar(v_e_1924_);
                if v___x_1927_ == 0 {
                    v___x_1928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1928_, 0, v_e_1924_);
                    return v___x_1928_;
                } else {
                    v___x_1929_ = lean_st_ref_get(v___y_1925_);
                    v_mctx_1930_ = crate::leanh::lean_ctor_get(v___x_1929_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1930_);
                    crate::leanh::lean_dec(v___x_1929_);
                    v___x_1931_ = l_Lean_instantiateMVarsCore(v_mctx_1930_, v_e_1924_);
                    v_fst_1932_ = crate::leanh::lean_ctor_get(v___x_1931_, 0);
                    crate::leanh::lean_inc(v_fst_1932_);
                    v_snd_1933_ = crate::leanh::lean_ctor_get(v___x_1931_, 1);
                    crate::leanh::lean_inc(v_snd_1933_);
                    crate::leanh::lean_dec_ref(v___x_1931_);
                    v___x_1934_ = lean_st_ref_take(v___y_1925_);
                    v_cache_1935_ = crate::leanh::lean_ctor_get(v___x_1934_, 1);
                    v_zetaDeltaFVarIds_1936_ = crate::leanh::lean_ctor_get(v___x_1934_, 2);
                    v_postponed_1937_ = crate::leanh::lean_ctor_get(v___x_1934_, 3);
                    v_diag_1938_ = crate::leanh::lean_ctor_get(v___x_1934_, 4);
                    v_isSharedCheck_1947_ = (!crate::leanh::lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v_unused_1948_ = crate::leanh::lean_ctor_get(v___x_1934_, 0);
                        crate::leanh::lean_dec(v_unused_1948_);
                        v___x_1940_ = v___x_1934_;
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1938_);
                        crate::leanh::lean_inc(v_postponed_1937_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1936_);
                        crate::leanh::lean_inc(v_cache_1935_);
                        crate::leanh::lean_dec(v___x_1934_);
                        v___x_1940_ = crate::leanh::lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1940_, 0, v_snd_1933_);
                    v___x_1943_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_snd_1933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_cache_1935_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1946_,
                        2,
                        v_zetaDeltaFVarIds_1936_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_postponed_1937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_diag_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1944_ = lean_st_ref_set(v___y_1925_, v___x_1943_);
                v___x_1945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1945_, 0, v_fst_1932_);
                return v___x_1945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(
    mut v_e_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1949_, v___y_1950_);
    crate::leanh::lean_dec(v___y_1950_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(
    mut v_e_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1953_, v___y_1957_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(
    mut v_e_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
    mut v___y_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(v_e_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    crate::leanh::lean_dec(v___y_1968_);
    crate::leanh::lean_dec_ref(v___y_1967_);
    crate::leanh::lean_dec(v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v___y_1964_);
    crate::leanh::lean_dec_ref(v___y_1963_);
    return v_res_1970_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(
    mut v_msgData_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = lean_st_ref_get(v___y_1975_);
    v_env_1978_ = crate::leanh::lean_ctor_get(v___x_1977_, 0);
    crate::leanh::lean_inc_ref(v_env_1978_);
    crate::leanh::lean_dec(v___x_1977_);
    v___x_1979_ = lean_st_ref_get(v___y_1973_);
    v_mctx_1980_ = crate::leanh::lean_ctor_get(v___x_1979_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1980_);
    crate::leanh::lean_dec(v___x_1979_);
    v_lctx_1981_ = crate::leanh::lean_ctor_get(v___y_1972_, 2);
    v_options_1982_ = crate::leanh::lean_ctor_get(v___y_1974_, 2);
    crate::leanh::lean_inc_ref(v_options_1982_);
    crate::leanh::lean_inc_ref(v_lctx_1981_);
    v___x_1983_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1983_, 0, v_env_1978_);
    crate::leanh::lean_ctor_set(v___x_1983_, 1, v_mctx_1980_);
    crate::leanh::lean_ctor_set(v___x_1983_, 2, v_lctx_1981_);
    crate::leanh::lean_ctor_set(v___x_1983_, 3, v_options_1982_);
    v___x_1984_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1984_, 0, v___x_1983_);
    crate::leanh::lean_ctor_set(v___x_1984_, 1, v_msgData_1971_);
    v___x_1985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(
    mut v_msgData_1986_: *mut crate::leanh::LeanObject,
    mut v___y_1987_: *mut crate::leanh::LeanObject,
    mut v___y_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msgData_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    crate::leanh::lean_dec(v___y_1988_);
    crate::leanh::lean_dec_ref(v___y_1987_);
    return v_res_1992_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1993_ = crate::leanh::lean_box(1);
    v___x_1994_ = l_Lean_MessageData_ofFormat(v___x_1993_);
    return v___x_1994_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2;
    v___x_1999_ = l_Lean_MessageData_ofFormat(v___x_1998_);
    return v___x_1999_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(
    mut v_x_2000_: *mut crate::leanh::LeanObject,
    mut v_x_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v_before_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_unused_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2001_) == 0 {
                    return v_x_2000_;
                } else {
                    v_head_2002_ = crate::leanh::lean_ctor_get(v_x_2001_, 0);
                    v_tail_2003_ = crate::leanh::lean_ctor_get(v_x_2001_, 1);
                    v_isSharedCheck_2025_ = (!crate::leanh::lean_is_exclusive(v_x_2001_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2005_ = v_x_2001_;
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2003_);
                        crate::leanh::lean_inc(v_head_2002_);
                        crate::leanh::lean_dec(v_x_2001_);
                        v___x_2005_ = crate::leanh::lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2007_ = crate::leanh::lean_ctor_get(v_head_2002_, 0);
                v_isSharedCheck_2023_ = (!crate::leanh::lean_is_exclusive(v_head_2002_)) as u8;
                if v_isSharedCheck_2023_ == 0 {
                    v_unused_2024_ = crate::leanh::lean_ctor_get(v_head_2002_, 1);
                    crate::leanh::lean_dec(v_unused_2024_);
                    v___x_2009_ = v_head_2002_;
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2007_);
                    crate::leanh::lean_dec(v_head_2002_);
                    v___x_2009_ = crate::leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2011_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2010_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2009_, 7);
                    crate::leanh::lean_ctor_set(v___x_2009_, 1, v___x_2011_);
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v_x_2000_);
                    v___x_2013_ = v___x_2009_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_x_2000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3);
                if v_isShared_2006_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2005_, 7);
                    crate::leanh::lean_ctor_set(v___x_2005_, 1, v___x_2014_);
                    crate::leanh::lean_ctor_set(v___x_2005_, 0, v___x_2013_);
                    v___x_2016_ = v___x_2005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2014_);
                    v___x_2016_ = v_reuseFailAlloc_2021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2017_ = l_Lean_MessageData_ofSyntax(v_before_2007_);
                v___x_2018_ = l_Lean_indentD(v___x_2017_);
                v___x_2019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_2016_);
                crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                v_x_2000_ = v___x_2019_;
                v_x_2001_ = v_tail_2003_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(
    mut v_opts_2026_: *mut crate::leanh::LeanObject,
    mut v_opt_2027_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2028_ = crate::leanh::lean_ctor_get(v_opt_2027_, 0);
    v_defValue_2029_ = crate::leanh::lean_ctor_get(v_opt_2027_, 1);
    v_map_2030_ = crate::leanh::lean_ctor_get(v_opts_2026_, 0);
    v___x_2031_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2030_,
            v_name_2028_,
        );
    if crate::leanh::lean_obj_tag(v___x_2031_) == 0 {
        let mut v___x_2032_: u8 = 0;
        v___x_2032_ = (crate::leanh::lean_unbox(v_defValue_2029_) as u8);
        return v___x_2032_;
    } else {
        let mut v_val_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2033_ = crate::leanh::lean_ctor_get(v___x_2031_, 0);
        crate::leanh::lean_inc(v_val_2033_);
        crate::leanh::lean_dec_ref_known(v___x_2031_, 1);
        if crate::leanh::lean_obj_tag(v_val_2033_) == 1 {
            let mut v_v_2034_: u8 = 0;
            v_v_2034_ = crate::leanh::lean_ctor_get_uint8(v_val_2033_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2033_, 0);
            return v_v_2034_;
        } else {
            let mut v___x_2035_: u8 = 0;
            crate::leanh::lean_dec(v_val_2033_);
            v___x_2035_ = (crate::leanh::lean_unbox(v_defValue_2029_) as u8);
            return v___x_2035_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(
    mut v_opts_2036_: *mut crate::leanh::LeanObject,
    mut v_opt_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: u8 = 0;
    let mut v_r_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_opts_2036_, v_opt_2037_);
    crate::leanh::lean_dec_ref(v_opt_2037_);
    crate::leanh::lean_dec_ref(v_opts_2036_);
    v_r_2039_ = crate::leanh::lean_box((v_res_2038_) as usize);
    return v_r_2039_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1;
    v___x_2044_ = l_Lean_MessageData_ofFormat(v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(
    mut v_msgData_2045_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2046_: *mut crate::leanh::LeanObject,
    mut v___y_2047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2049_ = crate::leanh::lean_ctor_get(v___y_2047_, 2);
                v___x_2050_ = l_Lean_Elab_pp_macroStack;
                v___x_2051_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_options_2049_, v___x_2050_);
                if v___x_2051_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2046_);
                    v___x_2052_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v_msgData_2045_);
                    return v___x_2052_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2046_) == 0 {
                        v___x_2053_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2053_, 0, v_msgData_2045_);
                        return v___x_2053_;
                    } else {
                        v_head_2054_ = crate::leanh::lean_ctor_get(v_macroStack_2046_, 0);
                        crate::leanh::lean_inc(v_head_2054_);
                        v_after_2055_ = crate::leanh::lean_ctor_get(v_head_2054_, 1);
                        v_isSharedCheck_2070_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2054_)) as u8;
                        if v_isSharedCheck_2070_ == 0 {
                            v_unused_2071_ = crate::leanh::lean_ctor_get(v_head_2054_, 0);
                            crate::leanh::lean_dec(v_unused_2071_);
                            v___x_2057_ = v_head_2054_;
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2055_);
                            crate::leanh::lean_dec(v_head_2054_);
                            v___x_2057_ = crate::leanh::lean_box(0);
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2059_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2058_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2057_, 7);
                    crate::leanh::lean_ctor_set(v___x_2057_, 1, v___x_2059_);
                    crate::leanh::lean_ctor_set(v___x_2057_, 0, v_msgData_2045_);
                    v___x_2061_ = v___x_2057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_msgData_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2059_);
                    v___x_2061_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2062_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2);
                v___x_2063_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                crate::leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                v___x_2064_ = l_Lean_MessageData_ofSyntax(v_after_2055_);
                v___x_2065_ = l_Lean_indentD(v___x_2064_);
                v_msgData_2066_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2066_, 0, v___x_2063_);
                crate::leanh::lean_ctor_set(v_msgData_2066_, 1, v___x_2065_);
                v___x_2067_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(v_msgData_2066_, v_macroStack_2046_);
                v___x_2068_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2068_, 0, v___x_2067_);
                return v___x_2068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(
    mut v_msgData_2072_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2073_: *mut crate::leanh::LeanObject,
    mut v___y_2074_: *mut crate::leanh::LeanObject,
    mut v___y_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2072_, v_macroStack_2073_, v___y_2074_);
    crate::leanh::lean_dec_ref(v___y_2074_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(
    mut v_msg_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2085_ = crate::leanh::lean_ctor_get(v___y_2082_, 5);
                v___x_2086_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msg_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
                v_a_2087_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
                crate::leanh::lean_inc(v_a_2087_);
                crate::leanh::lean_dec_ref(v___x_2086_);
                v_macroStack_2088_ = crate::leanh::lean_ctor_get(v___y_2078_, 1);
                v___x_2089_ = l_Lean_Elab_getBetterRef(v_ref_2085_, v_macroStack_2088_);
                crate::leanh::lean_inc(v_macroStack_2088_);
                v___x_2090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_a_2087_, v_macroStack_2088_, v___y_2082_);
                v_a_2091_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
                v_isSharedCheck_2099_ = (!crate::leanh::lean_is_exclusive(v___x_2090_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2093_ = v___x_2090_;
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2091_);
                    crate::leanh::lean_dec(v___x_2090_);
                    v___x_2093_ = crate::leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2095_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2089_);
                crate::leanh::lean_ctor_set(v___x_2095_, 1, v_a_2091_);
                if v_isShared_2094_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2093_, 1);
                    crate::leanh::lean_ctor_set(v___x_2093_, 0, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
                    v___x_2097_ = v_reuseFailAlloc_2098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg___boxed(
    mut v_msg_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
    mut v___y_2104_: *mut crate::leanh::LeanObject,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
    mut v___y_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    crate::leanh::lean_dec(v___y_2106_);
    crate::leanh::lean_dec_ref(v___y_2105_);
    crate::leanh::lean_dec(v___y_2104_);
    crate::leanh::lean_dec_ref(v___y_2103_);
    crate::leanh::lean_dec(v___y_2102_);
    crate::leanh::lean_dec_ref(v___y_2101_);
    return v_res_2108_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12;
    v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
    mut v_x_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2171_: u8 = 0;
    let mut v_cancelTk_x3f_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2173_: u8 = 0;
    let mut v_inheritedTraceOptions_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_a_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2156_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
                crate::leanh::lean_inc(v_x_2148_);
                v___x_2157_ = l_Lean_Syntax_isOfKind(v_x_2148_, v___x_2156_);
                if v___x_2157_ == 0 {
                    crate::leanh::lean_dec(v_x_2148_);
                    v___x_2158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
                    return v___x_2158_;
                } else {
                    v_fileName_2159_ = crate::leanh::lean_ctor_get(v_a_2153_, 0);
                    v_fileMap_2160_ = crate::leanh::lean_ctor_get(v_a_2153_, 1);
                    v_options_2161_ = crate::leanh::lean_ctor_get(v_a_2153_, 2);
                    v_currRecDepth_2162_ = crate::leanh::lean_ctor_get(v_a_2153_, 3);
                    v_maxRecDepth_2163_ = crate::leanh::lean_ctor_get(v_a_2153_, 4);
                    v_ref_2164_ = crate::leanh::lean_ctor_get(v_a_2153_, 5);
                    v_currNamespace_2165_ = crate::leanh::lean_ctor_get(v_a_2153_, 6);
                    v_openDecls_2166_ = crate::leanh::lean_ctor_get(v_a_2153_, 7);
                    v_initHeartbeats_2167_ = crate::leanh::lean_ctor_get(v_a_2153_, 8);
                    v_maxHeartbeats_2168_ = crate::leanh::lean_ctor_get(v_a_2153_, 9);
                    v_quotContext_2169_ = crate::leanh::lean_ctor_get(v_a_2153_, 10);
                    v_currMacroScope_2170_ = crate::leanh::lean_ctor_get(v_a_2153_, 11);
                    v_diag_2171_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_2172_ = crate::leanh::lean_ctor_get(v_a_2153_, 12);
                    v_suppressElabErrors_2173_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_2174_ = crate::leanh::lean_ctor_get(v_a_2153_, 13);
                    v___x_2175_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2176_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2175_);
                    v___x_2177_ = crate::leanh::lean_box(0);
                    v_ref_2178_ = l_Lean_replaceRef(v___x_2176_, v_ref_2164_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2174_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2172_);
                    crate::leanh::lean_inc(v_currMacroScope_2170_);
                    crate::leanh::lean_inc(v_quotContext_2169_);
                    crate::leanh::lean_inc(v_maxHeartbeats_2168_);
                    crate::leanh::lean_inc(v_initHeartbeats_2167_);
                    crate::leanh::lean_inc(v_openDecls_2166_);
                    crate::leanh::lean_inc(v_currNamespace_2165_);
                    crate::leanh::lean_inc(v_maxRecDepth_2163_);
                    crate::leanh::lean_inc(v_currRecDepth_2162_);
                    crate::leanh::lean_inc_ref(v_options_2161_);
                    crate::leanh::lean_inc_ref(v_fileMap_2160_);
                    crate::leanh::lean_inc_ref(v_fileName_2159_);
                    v___x_2179_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_2179_, 0, v_fileName_2159_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 1, v_fileMap_2160_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 2, v_options_2161_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 3, v_currRecDepth_2162_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 4, v_maxRecDepth_2163_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 5, v_ref_2178_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 6, v_currNamespace_2165_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 7, v_openDecls_2166_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 8, v_initHeartbeats_2167_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 9, v_maxHeartbeats_2168_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 10, v_quotContext_2169_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 11, v_currMacroScope_2170_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 12, v_cancelTk_x3f_2172_);
                    crate::leanh::lean_ctor_set(v___x_2179_, 13, v_inheritedTraceOptions_2174_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_2171_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_2173_,
                    );
                    v___x_2180_ = l_Lean_Elab_Term_elabTerm(
                        v___x_2176_,
                        v___x_2177_,
                        v___x_2157_,
                        v___x_2157_,
                        v_a_2149_,
                        v_a_2150_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2180_) == 0 {
                        v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                        crate::leanh::lean_inc_n(v_a_2181_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2180_, 1);
                        crate::leanh::lean_inc(v_a_2154_);
                        crate::leanh::lean_inc_ref(v___x_2179_);
                        crate::leanh::lean_inc(v_a_2152_);
                        crate::leanh::lean_inc_ref(v_a_2151_);
                        v___x_2182_ = lean_infer_type(
                            v_a_2181_,
                            v_a_2151_,
                            v_a_2152_,
                            v___x_2179_,
                            v_a_2154_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2182_) == 0 {
                            v_a_2183_ = crate::leanh::lean_ctor_get(v___x_2182_, 0);
                            crate::leanh::lean_inc_n(v_a_2183_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_2182_, 1);
                            v___x_2184_ = l_Lean_Elab_Term_tryPostponeIfMVar(
                                v_a_2183_,
                                v_a_2149_,
                                v_a_2150_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2184_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2184_, 1);
                                v___x_2185_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_a_2183_, v_a_2152_);
                                v_a_2186_ = crate::leanh::lean_ctor_get(v___x_2185_, 0);
                                v_isSharedCheck_2319_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2185_)) as u8;
                                if v_isSharedCheck_2319_ == 0 {
                                    v___x_2188_ = v___x_2185_;
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2186_);
                                    crate::leanh::lean_dec(v___x_2185_);
                                    v___x_2188_ = crate::leanh::lean_box(0);
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2183_);
                                crate::leanh::lean_dec(v_a_2181_);
                                crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                                crate::leanh::lean_dec(v_x_2148_);
                                v_a_2320_ = crate::leanh::lean_ctor_get(v___x_2184_, 0);
                                v_isSharedCheck_2327_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2184_)) as u8;
                                if v_isSharedCheck_2327_ == 0 {
                                    v___x_2322_ = v___x_2184_;
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2320_);
                                    crate::leanh::lean_dec(v___x_2184_);
                                    v___x_2322_ = crate::leanh::lean_box(0);
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2181_);
                            crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                            crate::leanh::lean_dec(v_x_2148_);
                            return v___x_2182_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                        crate::leanh::lean_dec(v_x_2148_);
                        return v___x_2180_;
                    }
                }
            }
            1 => {
                v___x_2190_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2191_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2190_);
                v___x_2192_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_2193_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2192_);
                crate::leanh::lean_dec(v_x_2148_);
                v___x_2254_ = l_Lean_Expr_consumeMData(v_a_2186_);
                if crate::leanh::lean_obj_tag(v___x_2254_) == 5 {
                    v_fn_2255_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                    crate::leanh::lean_inc_ref(v_fn_2255_);
                    v_arg_2256_ = crate::leanh::lean_ctor_get(v___x_2254_, 1);
                    crate::leanh::lean_inc_ref_n(v_arg_2256_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2254_, 2);
                    v___x_2257_ = l_Lean_Meta_getLevel(
                        v_arg_2256_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2257_) == 0 {
                        v_a_2258_ = crate::leanh::lean_ctor_get(v___x_2257_, 0);
                        crate::leanh::lean_inc(v_a_2258_);
                        crate::leanh::lean_dec_ref_known(v___x_2257_, 1);
                        v___x_2259_ = l_Lean_Level_dec(v_a_2258_);
                        crate::leanh::lean_dec(v_a_2258_);
                        if crate::leanh::lean_obj_tag(v___x_2259_) == 1 {
                            v_val_2260_ = crate::leanh::lean_ctor_get(v___x_2259_, 0);
                            crate::leanh::lean_inc(v_val_2260_);
                            crate::leanh::lean_dec_ref_known(v___x_2259_, 1);
                            crate::leanh::lean_inc(v_a_2186_);
                            v___x_2261_ = l_Lean_Meta_getLevel(
                                v_a_2186_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2261_) == 0 {
                                v_a_2262_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                                crate::leanh::lean_inc(v_a_2262_);
                                crate::leanh::lean_dec_ref_known(v___x_2261_, 1);
                                v___x_2263_ = l_Lean_Level_dec(v_a_2262_);
                                crate::leanh::lean_dec(v_a_2262_);
                                if crate::leanh::lean_obj_tag(v___x_2263_) == 1 {
                                    crate::leanh::lean_dec(v_a_2186_);
                                    v_val_2264_ = crate::leanh::lean_ctor_get(v___x_2263_, 0);
                                    v_isSharedCheck_2286_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2263_)) as u8;
                                    if v_isSharedCheck_2286_ == 0 {
                                        v___x_2266_ = v___x_2263_;
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_2264_);
                                        crate::leanh::lean_dec(v___x_2263_);
                                        v___x_2266_ = crate::leanh::lean_box(0);
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_2263_);
                                    crate::leanh::lean_dec(v_val_2260_);
                                    crate::leanh::lean_dec_ref(v_arg_2256_);
                                    crate::leanh::lean_dec_ref(v_fn_2255_);
                                    crate::leanh::lean_dec(v___x_2193_);
                                    crate::leanh::lean_dec(v___x_2191_);
                                    crate::leanh::lean_del_object(v___x_2188_);
                                    crate::leanh::lean_dec(v_a_2181_);
                                    v___x_2287_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                                    v___x_2288_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                                    v___x_2289_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2287_);
                                    crate::leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
                                    v___x_2290_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2289_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                                    crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                                    v___y_2245_ = v___x_2290_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_2260_);
                                crate::leanh::lean_dec_ref(v_arg_2256_);
                                crate::leanh::lean_dec_ref(v_fn_2255_);
                                crate::leanh::lean_dec(v___x_2193_);
                                crate::leanh::lean_dec(v___x_2191_);
                                crate::leanh::lean_del_object(v___x_2188_);
                                crate::leanh::lean_dec(v_a_2186_);
                                crate::leanh::lean_dec(v_a_2181_);
                                crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                                v_a_2291_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                                v_isSharedCheck_2298_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2261_)) as u8;
                                if v_isSharedCheck_2298_ == 0 {
                                    v___x_2293_ = v___x_2261_;
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2291_);
                                    crate::leanh::lean_dec(v___x_2261_);
                                    v___x_2293_ = crate::leanh::lean_box(0);
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2259_);
                            crate::leanh::lean_dec_ref(v_arg_2256_);
                            crate::leanh::lean_dec_ref(v_fn_2255_);
                            crate::leanh::lean_dec(v___x_2193_);
                            crate::leanh::lean_dec(v___x_2191_);
                            crate::leanh::lean_del_object(v___x_2188_);
                            crate::leanh::lean_dec(v_a_2181_);
                            v___x_2299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                            v___x_2300_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                            v___x_2301_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2299_);
                            crate::leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                            v___x_2302_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2301_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                            crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                            v___y_2245_ = v___x_2302_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_2256_);
                        crate::leanh::lean_dec_ref(v_fn_2255_);
                        crate::leanh::lean_dec(v___x_2193_);
                        crate::leanh::lean_dec(v___x_2191_);
                        crate::leanh::lean_del_object(v___x_2188_);
                        crate::leanh::lean_dec(v_a_2186_);
                        crate::leanh::lean_dec(v_a_2181_);
                        crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                        v_a_2303_ = crate::leanh::lean_ctor_get(v___x_2257_, 0);
                        v_isSharedCheck_2310_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2257_)) as u8;
                        if v_isSharedCheck_2310_ == 0 {
                            v___x_2305_ = v___x_2257_;
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2303_);
                            crate::leanh::lean_dec(v___x_2257_);
                            v___x_2305_ = crate::leanh::lean_box(0);
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2254_);
                    crate::leanh::lean_dec(v___x_2193_);
                    crate::leanh::lean_dec(v___x_2191_);
                    crate::leanh::lean_del_object(v___x_2188_);
                    v___x_2311_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15);
                    v___x_2312_ = l_Lean_MessageData_ofExpr(v_a_2181_);
                    v___x_2313_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2311_);
                    crate::leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                    v___x_2314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17);
                    v___x_2315_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                    v___x_2317_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2315_);
                    crate::leanh::lean_ctor_set(v___x_2317_, 1, v___x_2316_);
                    v___x_2318_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2317_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                    crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                    v___y_2245_ = v___x_2318_;
                    state = 8;
                    continue;
                }
            }
            2 => {
                v___x_2202_ = 0;
                v___x_2203_ = l_Lean_SourceInfo_fromRef(v_ref_2164_, v___x_2202_);
                v___x_2204_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3;
                v___x_2205_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2;
                crate::leanh::lean_inc_n(v___x_2203_, 2);
                v___x_2206_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2206_, 0, v___x_2203_);
                crate::leanh::lean_ctor_set(v___x_2206_, 1, v___x_2205_);
                v___x_2207_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_2208_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2208_, 0, v___x_2203_);
                crate::leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
                v___x_2209_ = l_Lean_Syntax_node3(
                    v___x_2203_,
                    v___x_2204_,
                    v___x_2206_,
                    v___x_2191_,
                    v___x_2208_,
                );
                v___x_2210_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4;
                v___x_2211_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_fst_2195_);
                v___x_2212_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2212_, 0, v_fst_2195_);
                crate::leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
                crate::leanh::lean_inc_ref(v___x_2212_);
                v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
                crate::leanh::lean_inc_ref(v_fst_2199_);
                v___x_2214_ = l_Lean_Expr_app___override(v___x_2213_, v_fst_2199_);
                if v_isShared_2189_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2188_, 1);
                    crate::leanh::lean_ctor_set(v___x_2188_, 0, v___x_2214_);
                    v___x_2216_ = v___x_2188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2214_);
                    v___x_2216_ = v_reuseFailAlloc_2243_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2217_ = l_Lean_Elab_Term_elabTerm(
                    v___x_2209_,
                    v___x_2216_,
                    v___x_2157_,
                    v___x_2157_,
                    v_a_2149_,
                    v_a_2150_,
                    v_a_2151_,
                    v_a_2152_,
                    v_a_2153_,
                    v_a_2154_,
                );
                if crate::leanh::lean_obj_tag(v___x_2217_) == 0 {
                    v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2217_, 0);
                    v_isSharedCheck_2242_ = (!crate::leanh::lean_is_exclusive(v___x_2217_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2220_ = v___x_2217_;
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2218_);
                        crate::leanh::lean_dec(v___x_2217_);
                        v___x_2220_ = crate::leanh::lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2212_, 2);
                    crate::leanh::lean_dec_ref(v_snd_2201_);
                    crate::leanh::lean_dec_ref(v_fst_2200_);
                    crate::leanh::lean_dec_ref(v_fst_2199_);
                    crate::leanh::lean_dec_ref(v_fst_2198_);
                    crate::leanh::lean_dec_ref(v_fst_2197_);
                    crate::leanh::lean_dec(v_fst_2196_);
                    crate::leanh::lean_dec(v_fst_2195_);
                    crate::leanh::lean_dec(v___x_2193_);
                    return v___x_2217_;
                }
            }
            4 => {
                v___x_2222_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5;
                v___x_2223_ = l_Lean_mkConst(v___x_2222_, v___x_2212_);
                crate::leanh::lean_inc_ref(v_fst_2199_);
                crate::leanh::lean_inc_ref(v_fst_2198_);
                v___x_2224_ = l_Lean_mkAppB(v___x_2223_, v_fst_2198_, v_fst_2199_);
                if v_isShared_2221_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2220_, 1);
                    crate::leanh::lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                    v___x_2226_ = v___x_2220_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2224_);
                    v___x_2226_ = v_reuseFailAlloc_2241_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2227_ = l_Lean_Elab_Term_elabTerm(
                    v___x_2193_,
                    v___x_2226_,
                    v___x_2157_,
                    v___x_2157_,
                    v_a_2149_,
                    v_a_2150_,
                    v_a_2151_,
                    v_a_2152_,
                    v_a_2153_,
                    v_a_2154_,
                );
                if crate::leanh::lean_obj_tag(v___x_2227_) == 0 {
                    v_a_2228_ = crate::leanh::lean_ctor_get(v___x_2227_, 0);
                    v_isSharedCheck_2240_ = (!crate::leanh::lean_is_exclusive(v___x_2227_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v___x_2230_ = v___x_2227_;
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2228_);
                        crate::leanh::lean_dec(v___x_2227_);
                        v___x_2230_ = crate::leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2218_);
                    crate::leanh::lean_dec_ref(v_snd_2201_);
                    crate::leanh::lean_dec_ref(v_fst_2200_);
                    crate::leanh::lean_dec_ref(v_fst_2199_);
                    crate::leanh::lean_dec_ref(v_fst_2198_);
                    crate::leanh::lean_dec_ref(v_fst_2197_);
                    crate::leanh::lean_dec(v_fst_2196_);
                    crate::leanh::lean_dec(v_fst_2195_);
                    return v___x_2227_;
                }
            }
            6 => {
                v___x_2232_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7;
                v___x_2233_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2233_, 0, v_fst_2196_);
                crate::leanh::lean_ctor_set(v___x_2233_, 1, v___x_2211_);
                v___x_2234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2234_, 0, v_fst_2195_);
                crate::leanh::lean_ctor_set(v___x_2234_, 1, v___x_2233_);
                v___x_2235_ = l_Lean_mkConst(v___x_2232_, v___x_2234_);
                v___x_2236_ = l_Lean_mkApp7(
                    v___x_2235_,
                    v_fst_2197_,
                    v_fst_2199_,
                    v_fst_2200_,
                    v_fst_2198_,
                    v_snd_2201_,
                    v_a_2218_,
                    v_a_2228_,
                );
                if v_isShared_2231_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2230_, 0, v___x_2236_);
                    v___x_2238_ = v___x_2230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2239_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2238_;
            }
            8 => {
                v_a_2246_ = crate::leanh::lean_ctor_get(v___y_2245_, 0);
                v_isSharedCheck_2253_ = (!crate::leanh::lean_is_exclusive(v___y_2245_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v___x_2248_ = v___y_2245_;
                    v_isShared_2249_ = v_isSharedCheck_2253_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2246_);
                    crate::leanh::lean_dec(v___y_2245_);
                    v___x_2248_ = crate::leanh::lean_box(0);
                    v_isShared_2249_ = v_isSharedCheck_2253_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2249_ == 0 {
                    v___x_2251_ = v___x_2248_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2252_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
                    v___x_2251_ = v_reuseFailAlloc_2252_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2251_;
            }
            11 => {
                v___x_2268_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9;
                v___x_2269_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_val_2260_);
                v___x_2270_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2270_, 0, v_val_2260_);
                crate::leanh::lean_ctor_set(v___x_2270_, 1, v___x_2269_);
                v___x_2271_ = l_Lean_mkConst(v___x_2268_, v___x_2270_);
                if v_isShared_2267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2266_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2266_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2285_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2274_ = 0;
                v___x_2275_ = crate::leanh::lean_box(0);
                v___x_2276_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_2273_,
                    v___x_2274_,
                    v___x_2275_,
                    v_a_2151_,
                    v_a_2152_,
                    v___x_2179_,
                    v_a_2154_,
                );
                if crate::leanh::lean_obj_tag(v___x_2276_) == 0 {
                    v_a_2277_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
                    crate::leanh::lean_inc_n(v_a_2277_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2276_, 1);
                    v___x_2278_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11;
                    crate::leanh::lean_inc(v_val_2264_);
                    v___x_2279_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2279_, 0, v_val_2264_);
                    crate::leanh::lean_ctor_set(v___x_2279_, 1, v___x_2269_);
                    crate::leanh::lean_inc(v_val_2260_);
                    v___x_2280_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2280_, 0, v_val_2260_);
                    crate::leanh::lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                    v___x_2281_ = l_Lean_mkConst(v___x_2278_, v___x_2280_);
                    crate::leanh::lean_inc_ref(v_fn_2255_);
                    v___x_2282_ = l_Lean_mkAppB(v___x_2281_, v_fn_2255_, v_a_2277_);
                    v___x_2283_ = l_Lean_Meta_synthInstance(
                        v___x_2282_,
                        v___x_2177_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                    if crate::leanh::lean_obj_tag(v___x_2283_) == 0 {
                        v_a_2284_ = crate::leanh::lean_ctor_get(v___x_2283_, 0);
                        crate::leanh::lean_inc(v_a_2284_);
                        crate::leanh::lean_dec_ref_known(v___x_2283_, 1);
                        v_fst_2195_ = v_val_2260_;
                        v_fst_2196_ = v_val_2264_;
                        v_fst_2197_ = v_fn_2255_;
                        v_fst_2198_ = v_arg_2256_;
                        v_fst_2199_ = v_a_2277_;
                        v_fst_2200_ = v_a_2284_;
                        v_snd_2201_ = v_a_2181_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_2277_);
                        crate::leanh::lean_dec(v_val_2264_);
                        crate::leanh::lean_dec(v_val_2260_);
                        crate::leanh::lean_dec_ref(v_arg_2256_);
                        crate::leanh::lean_dec_ref(v_fn_2255_);
                        crate::leanh::lean_dec(v___x_2193_);
                        crate::leanh::lean_dec(v___x_2191_);
                        crate::leanh::lean_del_object(v___x_2188_);
                        crate::leanh::lean_dec(v_a_2181_);
                        return v___x_2283_;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_2264_);
                    crate::leanh::lean_dec(v_val_2260_);
                    crate::leanh::lean_dec_ref(v_arg_2256_);
                    crate::leanh::lean_dec_ref(v_fn_2255_);
                    crate::leanh::lean_dec(v___x_2193_);
                    crate::leanh::lean_dec(v___x_2191_);
                    crate::leanh::lean_del_object(v___x_2188_);
                    crate::leanh::lean_dec(v_a_2181_);
                    crate::leanh::lean_dec_ref_known(v___x_2179_, 14);
                    return v___x_2276_;
                }
            }
            13 => {
                if v_isShared_2294_ == 0 {
                    v___x_2296_ = v___x_2293_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
                    v___x_2296_ = v_reuseFailAlloc_2297_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2296_;
            }
            15 => {
                if v_isShared_2306_ == 0 {
                    v___x_2308_ = v___x_2305_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2308_;
            }
            17 => {
                if v_isShared_2323_ == 0 {
                    v___x_2325_ = v___x_2322_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
                    v___x_2325_ = v_reuseFailAlloc_2326_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___boxed(
    mut v_x_2328_: *mut crate::leanh::LeanObject,
    mut v_a_2329_: *mut crate::leanh::LeanObject,
    mut v_a_2330_: *mut crate::leanh::LeanObject,
    mut v_a_2331_: *mut crate::leanh::LeanObject,
    mut v_a_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
    mut v_a_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2336_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_,
    );
    crate::leanh::lean_dec(v_a_2334_);
    crate::leanh::lean_dec_ref(v_a_2333_);
    crate::leanh::lean_dec(v_a_2332_);
    crate::leanh::lean_dec_ref(v_a_2331_);
    crate::leanh::lean_dec(v_a_2330_);
    crate::leanh::lean_dec_ref(v_a_2329_);
    return v_res_2336_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
    mut v_x_2337_: *mut crate::leanh::LeanObject,
    mut v_x_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2337_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_,
    );
    return v___x_2346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(
    mut v_x_2347_: *mut crate::leanh::LeanObject,
    mut v_x_2348_: *mut crate::leanh::LeanObject,
    mut v_a_2349_: *mut crate::leanh::LeanObject,
    mut v_a_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
        v_x_2347_, v_x_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_,
    );
    crate::leanh::lean_dec(v_a_2354_);
    crate::leanh::lean_dec_ref(v_a_2353_);
    crate::leanh::lean_dec(v_a_2352_);
    crate::leanh::lean_dec_ref(v_a_2351_);
    crate::leanh::lean_dec(v_a_2350_);
    crate::leanh::lean_dec_ref(v_a_2349_);
    crate::leanh::lean_dec(v_x_2348_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(
    mut v_00_u03b1_2357_: *mut crate::leanh::LeanObject,
    mut v_msg_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(
    mut v_00_u03b1_2367_: *mut crate::leanh::LeanObject,
    mut v_msg_2368_: *mut crate::leanh::LeanObject,
    mut v___y_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(v_00_u03b1_2367_, v_msg_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
    crate::leanh::lean_dec(v___y_2374_);
    crate::leanh::lean_dec_ref(v___y_2373_);
    crate::leanh::lean_dec(v___y_2372_);
    crate::leanh::lean_dec_ref(v___y_2371_);
    crate::leanh::lean_dec(v___y_2370_);
    crate::leanh::lean_dec_ref(v___y_2369_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(
    mut v_msgData_2377_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2377_, v_macroStack_2378_, v___y_2383_);
    return v___x_2386_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(
    mut v_msgData_2387_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(v_msgData_2387_, v_macroStack_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
    crate::leanh::lean_dec(v___y_2394_);
    crate::leanh::lean_dec_ref(v___y_2393_);
    crate::leanh::lean_dec(v___y_2392_);
    crate::leanh::lean_dec_ref(v___y_2391_);
    crate::leanh::lean_dec(v___y_2390_);
    crate::leanh::lean_dec_ref(v___y_2389_);
    return v_res_2396_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_2403_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
    v___x_2404_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1;
    v___x_2405_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed
            as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2406_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2402_,
        v___x_2403_,
        v___x_2404_,
        v___x_2405_,
    );
    return v___x_2406_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___boxed(
    mut v_a_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    return v_res_2408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Syntax(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Syntax(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
}
