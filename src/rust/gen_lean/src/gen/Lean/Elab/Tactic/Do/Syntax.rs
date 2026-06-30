// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Syntax
// Imports: Lean.Elab.BuiltinNotation Std.Do.Triple.Basic
use crate::ffi::{lean_infer_type, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::lean_mk_syntax_ident;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
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
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject,13979102795498516556 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut leanh::LeanObject,7932075773091973500 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut leanh::LeanObject,14296711813398647265 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut leanh::LeanObject,7043493786777132025 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut leanh::LeanObject,5346268661279150583 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut leanh::LeanObject,7306243862518720553 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value) as *mut leanh::LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut leanh::LeanObject,13332341187416043682 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut leanh::LeanObject,611622866940524098 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut leanh::LeanObject,300274991653824376 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut leanh::LeanObject,18105168627502861736 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut leanh::LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut leanh::LeanObject,16077784126176397009 as *mut leanh::LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value) as *mut leanh::LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value) as *mut leanh::LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value) as *mut leanh::LeanObject,12966880221525079621 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut leanh::LeanObject,11553573755926099728 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 10, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value) as *mut leanh::LeanObject,8463861479368259073 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value) as *mut leanh::LeanObject,2214559063752339918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 135, 147, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut leanh::LeanObject,3676176009791887579 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut leanh::LeanObject,5444244426488757208 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut leanh::LeanObject,5409699204079762053 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,14659826576719934041 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut leanh::LeanObject,6004524207281992990 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,9130596894474051559 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,7722122208264906652 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,14847410795624973596 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 78, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut leanh::LeanObject,17122680503757600671 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut leanh::LeanObject,2940964116523157683 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 11, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 63, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value) as *mut leanh::LeanObject,5101830612129297492 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 135, 147, 63, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut leanh::LeanObject,13156709450692335107 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut leanh::LeanObject,7425120582457359416 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 77, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut leanh::LeanObject,4163951709596513047 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value) as *mut leanh::LeanObject,13939969460734853986 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 114, 101, 100, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value) as *mut leanh::LeanObject,4155561471746556359 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut leanh::LeanObject,3393990892394863740 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value) as *mut leanh::LeanObject,11963640885769744415 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value) as *mut leanh::LeanObject,6471916472876379905 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 80, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value
) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value) as *mut leanh::LeanObject,6757038018435374033 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [87, 114, 111, 110, 103, 32, 108, 101, 118, 101, 108, 32, 48, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 121, 112, 101, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 121, 112, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut leanh::LeanObject,4122983324971754373 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20;
    v___x_1248_ = l_String_toRawSubstring_x27(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47()
-> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_1305_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_P_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v_ref_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v_ref_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v_ref_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_P_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v_ref_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1313_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3;
                leanh::lean_inc(v_x_1310_);
                v___x_1314_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1313_);
                if v___x_1314_ == 0 {
                    v___x_1315_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8;
                    leanh::lean_inc(v_x_1310_);
                    v___x_1316_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1315_);
                    if v___x_1316_ == 0 {
                        v___x_1317_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10;
                        leanh::lean_inc(v_x_1310_);
                        v___x_1318_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1317_);
                        if v___x_1318_ == 0 {
                            v___x_1319_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11;
                            v___x_1320_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12;
                            leanh::lean_inc(v_x_1310_);
                            v___x_1321_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1320_);
                            if v___x_1321_ == 0 {
                                v___x_1322_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14;
                                leanh::lean_inc(v_x_1310_);
                                v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1322_);
                                if v___x_1323_ == 0 {
                                    v___x_1324_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1324_, 0, v_x_1310_);
                                    return v___x_1324_;
                                } else {
                                    v___x_1325_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_1326_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1325_);
                                    v___x_1327_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                                    leanh::lean_inc(v___x_1326_);
                                    v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
                                    if v___x_1328_ == 0 {
                                        leanh::lean_dec(v___x_1326_);
                                        v___x_1329_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1329_, 0, v_x_1310_);
                                        return v___x_1329_;
                                    } else {
                                        v___x_1330_ = leanh::lean_unsigned_to_nat(1);
                                        v___x_1331_ =
                                            l_Lean_Syntax_getArg(v___x_1326_, v___x_1330_);
                                        leanh::lean_dec(v___x_1326_);
                                        v___x_1332_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                                        leanh::lean_inc(v___x_1331_);
                                        v___x_1333_ =
                                            l_Lean_Syntax_isOfKind(v___x_1331_, v___x_1332_);
                                        if v___x_1333_ == 0 {
                                            leanh::lean_dec(v___x_1331_);
                                            v___x_1334_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(v___x_1334_, 0, v_x_1310_);
                                            return v___x_1334_;
                                        } else {
                                            v___x_1335_ =
                                                l_Lean_Syntax_getArg(v___x_1331_, v___x_1325_);
                                            leanh::lean_dec(v___x_1331_);
                                            v___x_1336_ = leanh::lean_box(0);
                                            v___x_1337_ = l_Lean_Syntax_matchesIdent(
                                                v___x_1335_,
                                                v___x_1336_,
                                            );
                                            leanh::lean_dec(v___x_1335_);
                                            if v___x_1337_ == 0 {
                                                v___x_1338_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_1338_,
                                                    0,
                                                    v_x_1310_,
                                                );
                                                return v___x_1338_;
                                            } else {
                                                v___x_1339_ = leanh::lean_unsigned_to_nat(3);
                                                v___x_1340_ =
                                                    l_Lean_Syntax_getArg(v_x_1310_, v___x_1339_);
                                                leanh::lean_inc(v___x_1340_);
                                                v___x_1341_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1340_,
                                                    v___x_1330_,
                                                );
                                                if v___x_1341_ == 0 {
                                                    leanh::lean_dec(v___x_1340_);
                                                    v___x_1342_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
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
                                                    leanh::lean_dec(v_x_1310_);
                                                    v___x_1344_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1343_, v___y_1311_);
                                                    if leanh::lean_obj_tag(v___x_1344_) == 0
                                                    {
                                                        v_a_1345_ = leanh::lean_ctor_get(
                                                            v___x_1344_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_1372_ =
                                                            (!leanh::lean_is_exclusive(
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
                                                            leanh::lean_inc(v_a_1345_);
                                                            leanh::lean_dec(v___x_1344_);
                                                            v___x_1347_ = leanh::lean_box(0);
                                                            v_isShared_1348_ =
                                                                v_isSharedCheck_1372_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v___x_1340_);
                                                        return v___x_1344_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_1373_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1374_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1373_);
                                v___x_1375_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                                leanh::lean_inc(v___x_1374_);
                                v___x_1376_ = l_Lean_Syntax_isOfKind(v___x_1374_, v___x_1375_);
                                if v___x_1376_ == 0 {
                                    leanh::lean_dec(v___x_1374_);
                                    v___x_1377_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1377_, 0, v_x_1310_);
                                    return v___x_1377_;
                                } else {
                                    v___x_1378_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1373_);
                                    v___x_1380_ =
                                        l_Lean_Syntax_matchesNull(v___x_1379_, v___x_1378_);
                                    if v___x_1380_ == 0 {
                                        leanh::lean_dec(v___x_1374_);
                                        v___x_1381_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_1381_, 0, v_x_1310_);
                                        return v___x_1381_;
                                    } else {
                                        leanh::lean_dec(v_x_1310_);
                                        v___x_1382_ = leanh::lean_unsigned_to_nat(3);
                                        v_b_1383_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1382_);
                                        v___x_1384_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_b_1383_, v___y_1311_);
                                        if leanh::lean_obj_tag(v___x_1384_) == 0 {
                                            v_a_1385_ = leanh::lean_ctor_get(v___x_1384_, 0);
                                            v_isSharedCheck_1406_ =
                                                (!leanh::lean_is_exclusive(v___x_1384_))
                                                    as u8;
                                            if v_isSharedCheck_1406_ == 0 {
                                                v___x_1387_ = v___x_1384_;
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_1385_);
                                                leanh::lean_dec(v___x_1384_);
                                                v___x_1387_ = leanh::lean_box(0);
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v___x_1374_);
                                            return v___x_1384_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_1407_ = leanh::lean_unsigned_to_nat(3);
                            v_t_1408_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1407_);
                            v___x_1409_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_t_1408_, v___y_1311_);
                            if leanh::lean_obj_tag(v___x_1409_) == 0 {
                                v_a_1410_ = leanh::lean_ctor_get(v___x_1409_, 0);
                                leanh::lean_inc(v_a_1410_);
                                leanh::lean_dec_ref_known(v___x_1409_, 1);
                                v___x_1411_ = leanh::lean_unsigned_to_nat(5);
                                v_e_1412_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1411_);
                                v___x_1413_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_e_1412_, v___y_1311_);
                                if leanh::lean_obj_tag(v___x_1413_) == 0 {
                                    v_a_1414_ = leanh::lean_ctor_get(v___x_1413_, 0);
                                    v_isSharedCheck_1432_ =
                                        (!leanh::lean_is_exclusive(v___x_1413_)) as u8;
                                    if v_isSharedCheck_1432_ == 0 {
                                        v___x_1416_ = v___x_1413_;
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1414_);
                                        leanh::lean_dec(v___x_1413_);
                                        v___x_1416_ = leanh::lean_box(0);
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_1410_);
                                    leanh::lean_dec(v_x_1310_);
                                    return v___x_1413_;
                                }
                            } else {
                                leanh::lean_dec(v_x_1310_);
                                return v___x_1409_;
                            }
                        }
                    } else {
                        v___x_1433_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1434_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1433_);
                        v___x_1435_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                        leanh::lean_inc(v___x_1434_);
                        v___x_1436_ = l_Lean_Syntax_isOfKind(v___x_1434_, v___x_1435_);
                        if v___x_1436_ == 0 {
                            leanh::lean_dec(v___x_1434_);
                            v___x_1437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1437_, 0, v_x_1310_);
                            return v___x_1437_;
                        } else {
                            v___x_1438_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1439_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1438_);
                            leanh::lean_dec(v___x_1434_);
                            v___x_1440_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                            leanh::lean_inc(v___x_1439_);
                            v___x_1441_ = l_Lean_Syntax_isOfKind(v___x_1439_, v___x_1440_);
                            if v___x_1441_ == 0 {
                                leanh::lean_dec(v___x_1439_);
                                v___x_1442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1442_, 0, v_x_1310_);
                                return v___x_1442_;
                            } else {
                                v___x_1443_ = l_Lean_Syntax_getArg(v___x_1439_, v___x_1433_);
                                leanh::lean_dec(v___x_1439_);
                                v___x_1444_ = leanh::lean_box(0);
                                v___x_1445_ = l_Lean_Syntax_matchesIdent(v___x_1443_, v___x_1444_);
                                leanh::lean_dec(v___x_1443_);
                                if v___x_1445_ == 0 {
                                    v___x_1446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_1446_, 0, v_x_1310_);
                                    return v___x_1446_;
                                } else {
                                    v_P_1447_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1438_);
                                    leanh::lean_dec(v_x_1310_);
                                    v___x_1448_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1447_, v___y_1311_);
                                    if leanh::lean_obj_tag(v___x_1448_) == 0 {
                                        v_a_1449_ = leanh::lean_ctor_get(v___x_1448_, 0);
                                        v_isSharedCheck_1471_ =
                                            (!leanh::lean_is_exclusive(v___x_1448_)) as u8;
                                        if v_isSharedCheck_1471_ == 0 {
                                            v___x_1451_ = v___x_1448_;
                                            v_isShared_1452_ = v_isSharedCheck_1471_;
                                            state = 7;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_1449_);
                                            leanh::lean_dec(v___x_1448_);
                                            v___x_1451_ = leanh::lean_box(0);
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
                    v___x_1472_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1473_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1472_);
                    leanh::lean_dec(v_x_1310_);
                    v___x_1474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                    return v___x_1474_;
                }
            }
            1 => {
                v_ref_1349_ = leanh::lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1350_ = leanh::lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1351_ = leanh::lean_ctor_get(v___y_1311_, 11);
                v___x_1352_ = l_Lean_Syntax_getArg(v___x_1340_, v___x_1325_);
                leanh::lean_dec(v___x_1340_);
                v___x_1353_ = l_Lean_SourceInfo_fromRef(v_ref_1349_, v___x_1321_);
                v___x_1354_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                leanh::lean_inc_n(v___x_1353_, 7);
                v___x_1355_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1355_, 0, v___x_1353_);
                leanh::lean_ctor_set(v___x_1355_, 1, v___x_1354_);
                v___x_1356_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                leanh::lean_inc(v_currMacroScope_1351_);
                leanh::lean_inc(v_quotContext_1350_);
                v___x_1357_ =
                    l_Lean_addMacroScope(v_quotContext_1350_, v___x_1336_, v_currMacroScope_1351_);
                v___x_1358_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1359_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1359_, 0, v___x_1353_);
                leanh::lean_ctor_set(v___x_1359_, 1, v___x_1356_);
                leanh::lean_ctor_set(v___x_1359_, 2, v___x_1357_);
                leanh::lean_ctor_set(v___x_1359_, 3, v___x_1358_);
                v___x_1360_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1332_, v___x_1359_);
                v___x_1361_ =
                    l_Lean_Syntax_node2(v___x_1353_, v___x_1327_, v___x_1355_, v___x_1360_);
                v___x_1362_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41;
                v___x_1363_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1363_, 0, v___x_1353_);
                leanh::lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                v___x_1364_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1365_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1364_, v___x_1352_);
                v___x_1366_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1367_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1367_, 0, v___x_1353_);
                leanh::lean_ctor_set(v___x_1367_, 1, v___x_1366_);
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
                    leanh::lean_ctor_set(v___x_1347_, 0, v___x_1368_);
                    v___x_1370_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1370_;
            }
            3 => {
                v_ref_1389_ = leanh::lean_ctor_get(v___y_1311_, 5);
                v___x_1390_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1378_);
                leanh::lean_dec(v___x_1374_);
                v_xs_1391_ = l_Lean_Syntax_getArgs(v___x_1390_);
                leanh::lean_dec(v___x_1390_);
                v___x_1392_ = l_Lean_SourceInfo_fromRef(v_ref_1389_, v___x_1318_);
                leanh::lean_inc_n(v___x_1392_, 5);
                v___x_1393_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1393_, 0, v___x_1392_);
                leanh::lean_ctor_set(v___x_1393_, 1, v___x_1319_);
                v___x_1394_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1395_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                v___x_1396_ = l_Array_append___redArg(v___x_1395_, v_xs_1391_);
                leanh::lean_dec_ref(v_xs_1391_);
                v___x_1397_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1397_, 0, v___x_1392_);
                leanh::lean_ctor_set(v___x_1397_, 1, v___x_1394_);
                leanh::lean_ctor_set(v___x_1397_, 2, v___x_1396_);
                v___x_1398_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1398_, 0, v___x_1392_);
                leanh::lean_ctor_set(v___x_1398_, 1, v___x_1394_);
                leanh::lean_ctor_set(v___x_1398_, 2, v___x_1395_);
                v___x_1399_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1400_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1400_, 0, v___x_1392_);
                leanh::lean_ctor_set(v___x_1400_, 1, v___x_1399_);
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
                    leanh::lean_ctor_set(v___x_1387_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1404_;
            }
            5 => {
                v_ref_1418_ = leanh::lean_ctor_get(v___y_1311_, 5);
                v___x_1419_ = leanh::lean_unsigned_to_nat(1);
                v___x_1420_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1419_);
                leanh::lean_dec(v_x_1310_);
                v___x_1421_ = l_Lean_SourceInfo_fromRef(v_ref_1418_, v___x_1316_);
                v___x_1422_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49;
                leanh::lean_inc_n(v___x_1421_, 3);
                v___x_1423_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1423_, 0, v___x_1421_);
                leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
                v___x_1424_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50;
                v___x_1425_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1425_, 0, v___x_1421_);
                leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
                v___x_1426_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51;
                v___x_1427_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1427_, 0, v___x_1421_);
                leanh::lean_ctor_set(v___x_1427_, 1, v___x_1426_);
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
                    leanh::lean_ctor_set(v___x_1416_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1430_;
            }
            7 => {
                v_ref_1453_ = leanh::lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1454_ = leanh::lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1455_ = leanh::lean_ctor_get(v___y_1311_, 11);
                v___x_1456_ = l_Lean_SourceInfo_fromRef(v_ref_1453_, v___x_1314_);
                v___x_1457_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                leanh::lean_inc_n(v___x_1456_, 5);
                v___x_1458_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1458_, 0, v___x_1456_);
                leanh::lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                v___x_1459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                leanh::lean_inc(v_currMacroScope_1455_);
                leanh::lean_inc(v_quotContext_1454_);
                v___x_1460_ =
                    l_Lean_addMacroScope(v_quotContext_1454_, v___x_1444_, v_currMacroScope_1455_);
                v___x_1461_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1462_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1462_, 0, v___x_1456_);
                leanh::lean_ctor_set(v___x_1462_, 1, v___x_1459_);
                leanh::lean_ctor_set(v___x_1462_, 2, v___x_1460_);
                leanh::lean_ctor_set(v___x_1462_, 3, v___x_1461_);
                v___x_1463_ = l_Lean_Syntax_node1(v___x_1456_, v___x_1440_, v___x_1462_);
                v___x_1464_ =
                    l_Lean_Syntax_node2(v___x_1456_, v___x_1435_, v___x_1458_, v___x_1463_);
                v___x_1465_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1466_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1466_, 0, v___x_1456_);
                leanh::lean_ctor_set(v___x_1466_, 1, v___x_1465_);
                v___x_1467_ = l_Lean_Syntax_node3(
                    v___x_1456_,
                    v___x_1315_,
                    v___x_1464_,
                    v_a_1449_,
                    v___x_1466_,
                );
                if v_isShared_1452_ == 0 {
                    leanh::lean_ctor_set(v___x_1451_, 0, v___x_1467_);
                    v___x_1469_ = v___x_1451_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
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
    mut v_x_1475_: *mut leanh::LeanObject,
    mut v___y_1476_: *mut leanh::LeanObject,
    mut v___y_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1475_, v___y_1476_);
    leanh::lean_dec_ref(v___y_1476_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(
    mut v_child_1479_: *mut leanh::LeanObject,
    mut v_childIdx_1480_: *mut leanh::LeanObject,
    mut v_x_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
    mut v___y_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subExpr_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_optionsPerPos_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inPattern_1493_: u8 = 0;
    let mut v_depth_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctxInitIndices_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_subExpr_1489_ = leanh::lean_ctor_get(v___y_1482_, 3);
    v_optionsPerPos_1490_ = leanh::lean_ctor_get(v___y_1482_, 0);
    v_currNamespace_1491_ = leanh::lean_ctor_get(v___y_1482_, 1);
    v_openDecls_1492_ = leanh::lean_ctor_get(v___y_1482_, 2);
    v_inPattern_1493_ = leanh::lean_ctor_get_uint8(
        v___y_1482_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
    );
    v_depth_1494_ = leanh::lean_ctor_get(v___y_1482_, 4);
    v_lctxInitIndices_1495_ = leanh::lean_ctor_get(v___y_1482_, 5);
    v_pos_1496_ = leanh::lean_ctor_get(v_subExpr_1489_, 1);
    v___x_1497_ = l_Lean_SubExpr_Pos_push(v_pos_1496_, v_childIdx_1480_);
    v___x_1498_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1498_, 0, v_child_1479_);
    leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    leanh::lean_inc(v_lctxInitIndices_1495_);
    leanh::lean_inc(v_depth_1494_);
    leanh::lean_inc(v_openDecls_1492_);
    leanh::lean_inc(v_currNamespace_1491_);
    leanh::lean_inc(v_optionsPerPos_1490_);
    v___x_1499_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
    leanh::lean_ctor_set(v___x_1499_, 0, v_optionsPerPos_1490_);
    leanh::lean_ctor_set(v___x_1499_, 1, v_currNamespace_1491_);
    leanh::lean_ctor_set(v___x_1499_, 2, v_openDecls_1492_);
    leanh::lean_ctor_set(v___x_1499_, 3, v___x_1498_);
    leanh::lean_ctor_set(v___x_1499_, 4, v_depth_1494_);
    leanh::lean_ctor_set(v___x_1499_, 5, v_lctxInitIndices_1495_);
    leanh::lean_ctor_set_uint8(
        v___x_1499_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
        v_inPattern_1493_,
    );
    leanh::lean_inc(v___y_1487_);
    leanh::lean_inc_ref(v___y_1486_);
    leanh::lean_inc(v___y_1485_);
    leanh::lean_inc_ref(v___y_1484_);
    leanh::lean_inc(v___y_1483_);
    v___x_1500_ = leanh::lean_apply_7(
        v_x_1481_,
        v___x_1499_,
        v___y_1483_,
        v___y_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
        leanh::lean_box(0),
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(
    mut v_child_1501_: *mut leanh::LeanObject,
    mut v_childIdx_1502_: *mut leanh::LeanObject,
    mut v_x_1503_: *mut leanh::LeanObject,
    mut v___y_1504_: *mut leanh::LeanObject,
    mut v___y_1505_: *mut leanh::LeanObject,
    mut v___y_1506_: *mut leanh::LeanObject,
    mut v___y_1507_: *mut leanh::LeanObject,
    mut v___y_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
    mut v___y_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1501_, v_childIdx_1502_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
    leanh::lean_dec(v___y_1509_);
    leanh::lean_dec_ref(v___y_1508_);
    leanh::lean_dec(v___y_1507_);
    leanh::lean_dec_ref(v___y_1506_);
    leanh::lean_dec(v___y_1505_);
    leanh::lean_dec_ref(v___y_1504_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(
    mut v___y_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subExpr_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_subExpr_1514_ = leanh::lean_ctor_get(v___y_1512_, 3);
    v_expr_1515_ = leanh::lean_ctor_get(v_subExpr_1514_, 0);
    leanh::lean_inc_ref(v_expr_1515_);
    v___x_1516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1516_, 0, v_expr_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(
    mut v___y_1517_: *mut leanh::LeanObject,
    mut v___y_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1517_);
    leanh::lean_dec_ref(v___y_1517_);
    return v_res_1519_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(
    mut v_x_1520_: *mut leanh::LeanObject,
    mut v___y_1521_: *mut leanh::LeanObject,
    mut v___y_1522_: *mut leanh::LeanObject,
    mut v___y_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
    mut v___y_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1521_);
    v_a_1529_ = leanh::lean_ctor_get(v___x_1528_, 0);
    leanh::lean_inc(v_a_1529_);
    leanh::lean_dec_ref(v___x_1528_);
    v___x_1530_ = l_Lean_Expr_appArg_x21(v_a_1529_);
    leanh::lean_dec(v_a_1529_);
    v___x_1531_ = leanh::lean_unsigned_to_nat(1);
    v___x_1532_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v___x_1530_, v___x_1531_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(
    mut v_x_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
    leanh::lean_dec(v___y_1539_);
    leanh::lean_dec_ref(v___y_1538_);
    leanh::lean_dec(v___y_1537_);
    leanh::lean_dec_ref(v___y_1536_);
    leanh::lean_dec(v___y_1535_);
    leanh::lean_dec_ref(v___y_1534_);
    return v_res_1541_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5;
    v___x_1557_ = lean_mk_syntax_ident(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
    mut v_a_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_a_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
    mut v_a_1571_: *mut leanh::LeanObject,
    mut v_a_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v_ref_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v_ref_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_ref_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v_ref_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1574_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1575_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1574_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
                if leanh::lean_obj_tag(v___x_1575_) == 0 {
                    v_a_1576_ = leanh::lean_ctor_get(v___x_1575_, 0);
                    v_isSharedCheck_1647_ = (!leanh::lean_is_exclusive(v___x_1575_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1578_ = v___x_1575_;
                        v_isShared_1579_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1576_);
                        leanh::lean_dec(v___x_1575_);
                        v___x_1578_ = leanh::lean_box(0);
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
                leanh::lean_inc(v_a_1576_);
                v___x_1581_ = l_Lean_Syntax_isOfKind(v_a_1576_, v___x_1580_);
                if v___x_1581_ == 0 {
                    v_ref_1582_ = leanh::lean_ctor_get(v_a_1571_, 5);
                    v___x_1583_ = l_Lean_SourceInfo_fromRef(v_ref_1582_, v___x_1581_);
                    v___x_1584_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                    v___x_1586_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    leanh::lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Syntax_node1(v___x_1583_, v___x_1586_, v_a_1576_);
                    v___x_1588_ =
                        l_Lean_Syntax_node2(v___x_1583_, v___x_1584_, v___x_1585_, v___x_1587_);
                    if v_isShared_1579_ == 0 {
                        leanh::lean_ctor_set(v___x_1578_, 0, v___x_1588_);
                        v___x_1590_ = v___x_1578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1591_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
                        v___x_1590_ = v_reuseFailAlloc_1591_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1592_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1593_ = l_Lean_Syntax_getArg(v_a_1576_, v___x_1592_);
                    v___x_1594_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    leanh::lean_inc(v___x_1593_);
                    v___x_1595_ = l_Lean_Syntax_isOfKind(v___x_1593_, v___x_1594_);
                    if v___x_1595_ == 0 {
                        leanh::lean_dec(v___x_1593_);
                        v_ref_1596_ = leanh::lean_ctor_get(v_a_1571_, 5);
                        v___x_1597_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1595_);
                        v___x_1598_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1599_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                        v___x_1600_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        leanh::lean_inc(v___x_1597_);
                        v___x_1601_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1600_, v_a_1576_);
                        v___x_1602_ =
                            l_Lean_Syntax_node2(v___x_1597_, v___x_1598_, v___x_1599_, v___x_1601_);
                        if v_isShared_1579_ == 0 {
                            leanh::lean_ctor_set(v___x_1578_, 0, v___x_1602_);
                            v___x_1604_ = v___x_1578_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1605_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                            v___x_1604_ = v_reuseFailAlloc_1605_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1606_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1607_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1592_);
                        v___x_1608_ = l_Lean_Syntax_matchesNull(v___x_1607_, v___x_1606_);
                        if v___x_1608_ == 0 {
                            leanh::lean_dec(v___x_1593_);
                            v_ref_1609_ = leanh::lean_ctor_get(v_a_1571_, 5);
                            v___x_1610_ = l_Lean_SourceInfo_fromRef(v_ref_1609_, v___x_1608_);
                            v___x_1611_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                            v___x_1613_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            leanh::lean_inc(v___x_1610_);
                            v___x_1614_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1613_, v_a_1576_);
                            v___x_1615_ = l_Lean_Syntax_node2(
                                v___x_1610_,
                                v___x_1611_,
                                v___x_1612_,
                                v___x_1614_,
                            );
                            if v_isShared_1579_ == 0 {
                                leanh::lean_ctor_set(v___x_1578_, 0, v___x_1615_);
                                v___x_1617_ = v___x_1578_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1618_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
                                v___x_1617_ = v_reuseFailAlloc_1618_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1578_);
                            leanh::lean_dec(v_a_1576_);
                            v___x_1619_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1620_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1619_);
                            v___x_1621_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1620_, v_a_1571_);
                            if leanh::lean_obj_tag(v___x_1621_) == 0 {
                                v_a_1622_ = leanh::lean_ctor_get(v___x_1621_, 0);
                                v_isSharedCheck_1646_ =
                                    (!leanh::lean_is_exclusive(v___x_1621_)) as u8;
                                if v_isSharedCheck_1646_ == 0 {
                                    v___x_1624_ = v___x_1621_;
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1622_);
                                    leanh::lean_dec(v___x_1621_);
                                    v___x_1624_ = leanh::lean_box(0);
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_1593_);
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
                v_ref_1626_ = leanh::lean_ctor_get(v_a_1571_, 5);
                v___x_1627_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1606_);
                leanh::lean_dec(v___x_1593_);
                v___x_1628_ = l_Lean_Syntax_getArgs(v___x_1627_);
                leanh::lean_dec(v___x_1627_);
                v___x_1629_ = 0;
                v___x_1630_ = l_Lean_SourceInfo_fromRef(v_ref_1626_, v___x_1629_);
                v___x_1631_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8;
                v___x_1632_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                leanh::lean_inc_n(v___x_1630_, 4);
                v___x_1634_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1634_, 0, v___x_1630_);
                leanh::lean_ctor_set(v___x_1634_, 1, v___x_1632_);
                leanh::lean_ctor_set(v___x_1634_, 2, v___x_1633_);
                v___x_1635_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11;
                v___x_1636_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1636_, 0, v___x_1630_);
                leanh::lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                v___x_1637_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1638_ = l_Array_append___redArg(v___x_1633_, v___x_1628_);
                leanh::lean_dec_ref(v___x_1628_);
                v___x_1639_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1639_, 0, v___x_1630_);
                leanh::lean_ctor_set(v___x_1639_, 1, v___x_1637_);
                leanh::lean_ctor_set(v___x_1639_, 2, v___x_1638_);
                v___x_1640_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1641_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1641_, 0, v___x_1630_);
                leanh::lean_ctor_set(v___x_1641_, 1, v___x_1640_);
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
                    leanh::lean_ctor_set(v___x_1624_, 0, v___x_1642_);
                    v___x_1644_ = v___x_1624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
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
    mut v_a_1648_: *mut leanh::LeanObject,
    mut v_a_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
    mut v_a_1651_: *mut leanh::LeanObject,
    mut v_a_1652_: *mut leanh::LeanObject,
    mut v_a_1653_: *mut leanh::LeanObject,
    mut v_a_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1655_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
        v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_,
    );
    leanh::lean_dec(v_a_1653_);
    leanh::lean_dec_ref(v_a_1652_);
    leanh::lean_dec(v_a_1651_);
    leanh::lean_dec_ref(v_a_1650_);
    leanh::lean_dec(v_a_1649_);
    leanh::lean_dec_ref(v_a_1648_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1656_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
    mut v___y_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
    leanh::lean_dec(v___y_1669_);
    leanh::lean_dec_ref(v___y_1668_);
    leanh::lean_dec(v___y_1667_);
    leanh::lean_dec_ref(v___y_1666_);
    leanh::lean_dec(v___y_1665_);
    leanh::lean_dec_ref(v___y_1664_);
    return v_res_1671_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(
    mut v_00_u03b1_1672_: *mut leanh::LeanObject,
    mut v_child_1673_: *mut leanh::LeanObject,
    mut v_childIdx_1674_: *mut leanh::LeanObject,
    mut v_x_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1673_, v_childIdx_1674_, v_x_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(
    mut v_00_u03b1_1684_: *mut leanh::LeanObject,
    mut v_child_1685_: *mut leanh::LeanObject,
    mut v_childIdx_1686_: *mut leanh::LeanObject,
    mut v_x_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(v_00_u03b1_1684_, v_child_1685_, v_childIdx_1686_, v_x_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
    leanh::lean_dec(v___y_1693_);
    leanh::lean_dec_ref(v___y_1692_);
    leanh::lean_dec(v___y_1691_);
    leanh::lean_dec_ref(v___y_1690_);
    leanh::lean_dec(v___y_1689_);
    leanh::lean_dec_ref(v___y_1688_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(
    mut v_00_u03b1_1696_: *mut leanh::LeanObject,
    mut v_x_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
    mut v___y_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
    return v___x_1705_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(
    mut v_00_u03b1_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
    mut v___y_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
    mut v___y_1714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(v_00_u03b1_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
    leanh::lean_dec(v___y_1713_);
    leanh::lean_dec_ref(v___y_1712_);
    leanh::lean_dec(v___y_1711_);
    leanh::lean_dec_ref(v___y_1710_);
    leanh::lean_dec(v___y_1709_);
    leanh::lean_dec_ref(v___y_1708_);
    return v_res_1715_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(
    mut v_x_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
    mut v___y_1719_: *mut leanh::LeanObject,
    mut v___y_1720_: *mut leanh::LeanObject,
    mut v___y_1721_: *mut leanh::LeanObject,
    mut v___y_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1716_, v___y_1721_);
    return v___x_1724_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(
    mut v_x_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
    mut v___y_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    leanh::lean_dec(v___y_1731_);
    leanh::lean_dec_ref(v___y_1730_);
    leanh::lean_dec(v___y_1729_);
    leanh::lean_dec_ref(v___y_1728_);
    leanh::lean_dec(v___y_1727_);
    leanh::lean_dec_ref(v___y_1726_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1()
-> *mut leanh::LeanObject {
    let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1774_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0;
    v___x_1775_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15;
    v___x_1776_ = leanh::lean_alloc_closure(
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
    mut v_a_1778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1779_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    return v_res_1779_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1;
    v___x_1787_ = lean_mk_syntax_ident(v___x_1786_);
    return v___x_1787_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
    mut v_a_1794_: *mut leanh::LeanObject,
    mut v_a_1795_: *mut leanh::LeanObject,
    mut v_a_1796_: *mut leanh::LeanObject,
    mut v_a_1797_: *mut leanh::LeanObject,
    mut v_a_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v_ref_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v_ref_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v_ref_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v_ref_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1801_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1801_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
                if leanh::lean_obj_tag(v___x_1802_) == 0 {
                    v_a_1803_ = leanh::lean_ctor_get(v___x_1802_, 0);
                    v_isSharedCheck_1874_ = (!leanh::lean_is_exclusive(v___x_1802_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1805_ = v___x_1802_;
                        v_isShared_1806_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1803_);
                        leanh::lean_dec(v___x_1802_);
                        v___x_1805_ = leanh::lean_box(0);
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
                leanh::lean_inc(v_a_1803_);
                v___x_1808_ = l_Lean_Syntax_isOfKind(v_a_1803_, v___x_1807_);
                if v___x_1808_ == 0 {
                    v_ref_1809_ = leanh::lean_ctor_get(v_a_1798_, 5);
                    v___x_1810_ = l_Lean_SourceInfo_fromRef(v_ref_1809_, v___x_1808_);
                    v___x_1811_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                    v___x_1813_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    leanh::lean_inc(v___x_1810_);
                    v___x_1814_ = l_Lean_Syntax_node1(v___x_1810_, v___x_1813_, v_a_1803_);
                    v___x_1815_ =
                        l_Lean_Syntax_node2(v___x_1810_, v___x_1811_, v___x_1812_, v___x_1814_);
                    if v_isShared_1806_ == 0 {
                        leanh::lean_ctor_set(v___x_1805_, 0, v___x_1815_);
                        v___x_1817_ = v___x_1805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1818_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
                        v___x_1817_ = v_reuseFailAlloc_1818_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1819_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1820_ = l_Lean_Syntax_getArg(v_a_1803_, v___x_1819_);
                    v___x_1821_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    leanh::lean_inc(v___x_1820_);
                    v___x_1822_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1821_);
                    if v___x_1822_ == 0 {
                        leanh::lean_dec(v___x_1820_);
                        v_ref_1823_ = leanh::lean_ctor_get(v_a_1798_, 5);
                        v___x_1824_ = l_Lean_SourceInfo_fromRef(v_ref_1823_, v___x_1822_);
                        v___x_1825_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1826_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                        v___x_1827_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        leanh::lean_inc(v___x_1824_);
                        v___x_1828_ = l_Lean_Syntax_node1(v___x_1824_, v___x_1827_, v_a_1803_);
                        v___x_1829_ =
                            l_Lean_Syntax_node2(v___x_1824_, v___x_1825_, v___x_1826_, v___x_1828_);
                        if v_isShared_1806_ == 0 {
                            leanh::lean_ctor_set(v___x_1805_, 0, v___x_1829_);
                            v___x_1831_ = v___x_1805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1832_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                            v___x_1831_ = v_reuseFailAlloc_1832_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1833_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1834_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1819_);
                        v___x_1835_ = l_Lean_Syntax_matchesNull(v___x_1834_, v___x_1833_);
                        if v___x_1835_ == 0 {
                            leanh::lean_dec(v___x_1820_);
                            v_ref_1836_ = leanh::lean_ctor_get(v_a_1798_, 5);
                            v___x_1837_ = l_Lean_SourceInfo_fromRef(v_ref_1836_, v___x_1835_);
                            v___x_1838_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1839_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                            v___x_1840_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            leanh::lean_inc(v___x_1837_);
                            v___x_1841_ = l_Lean_Syntax_node1(v___x_1837_, v___x_1840_, v_a_1803_);
                            v___x_1842_ = l_Lean_Syntax_node2(
                                v___x_1837_,
                                v___x_1838_,
                                v___x_1839_,
                                v___x_1841_,
                            );
                            if v_isShared_1806_ == 0 {
                                leanh::lean_ctor_set(v___x_1805_, 0, v___x_1842_);
                                v___x_1844_ = v___x_1805_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1845_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
                                v___x_1844_ = v_reuseFailAlloc_1845_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1805_);
                            leanh::lean_dec(v_a_1803_);
                            v___x_1846_ = leanh::lean_unsigned_to_nat(3);
                            v___x_1847_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1846_);
                            v___x_1848_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1847_, v_a_1798_);
                            if leanh::lean_obj_tag(v___x_1848_) == 0 {
                                v_a_1849_ = leanh::lean_ctor_get(v___x_1848_, 0);
                                v_isSharedCheck_1873_ =
                                    (!leanh::lean_is_exclusive(v___x_1848_)) as u8;
                                if v_isSharedCheck_1873_ == 0 {
                                    v___x_1851_ = v___x_1848_;
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1849_);
                                    leanh::lean_dec(v___x_1848_);
                                    v___x_1851_ = leanh::lean_box(0);
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_1820_);
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
                v_ref_1853_ = leanh::lean_ctor_get(v_a_1798_, 5);
                v___x_1854_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1833_);
                leanh::lean_dec(v___x_1820_);
                v___x_1855_ = l_Lean_Syntax_getArgs(v___x_1854_);
                leanh::lean_dec(v___x_1854_);
                v___x_1856_ = 0;
                v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1856_);
                v___x_1858_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4;
                v___x_1859_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                leanh::lean_inc_n(v___x_1857_, 4);
                v___x_1861_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1861_, 0, v___x_1857_);
                leanh::lean_ctor_set(v___x_1861_, 1, v___x_1859_);
                leanh::lean_ctor_set(v___x_1861_, 2, v___x_1860_);
                v___x_1862_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5;
                v___x_1863_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1863_, 0, v___x_1857_);
                leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1865_ = l_Array_append___redArg(v___x_1860_, v___x_1855_);
                leanh::lean_dec_ref(v___x_1855_);
                v___x_1866_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1866_, 0, v___x_1857_);
                leanh::lean_ctor_set(v___x_1866_, 1, v___x_1864_);
                leanh::lean_ctor_set(v___x_1866_, 2, v___x_1865_);
                v___x_1867_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1868_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1868_, 0, v___x_1857_);
                leanh::lean_ctor_set(v___x_1868_, 1, v___x_1867_);
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
                    leanh::lean_ctor_set(v___x_1851_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1851_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
    mut v_a_1875_: *mut leanh::LeanObject,
    mut v_a_1876_: *mut leanh::LeanObject,
    mut v_a_1877_: *mut leanh::LeanObject,
    mut v_a_1878_: *mut leanh::LeanObject,
    mut v_a_1879_: *mut leanh::LeanObject,
    mut v_a_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1882_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
        v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_,
    );
    leanh::lean_dec(v_a_1880_);
    leanh::lean_dec_ref(v_a_1879_);
    leanh::lean_dec(v_a_1878_);
    leanh::lean_dec_ref(v_a_1877_);
    leanh::lean_dec(v_a_1876_);
    leanh::lean_dec_ref(v_a_1875_);
    return v_res_1882_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1()
-> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1892_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0;
    v___x_1893_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2;
    v___x_1894_ = leanh::lean_alloc_closure(
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
    mut v_a_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1897_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    return v_res_1897_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = leanh::lean_box(0);
    v___x_1899_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    leanh::lean_ctor_set(v___x_1900_, 1, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0);
    v___x_1903_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1903_, 0, v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(
    mut v___y_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v_res_1905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(
    mut v_00_u03b1_1906_: *mut leanh::LeanObject,
    mut v___y_1907_: *mut leanh::LeanObject,
    mut v___y_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v___x_1914_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(
    mut v_00_u03b1_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
    mut v___y_1919_: *mut leanh::LeanObject,
    mut v___y_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(v_00_u03b1_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
    leanh::lean_dec(v___y_1921_);
    leanh::lean_dec_ref(v___y_1920_);
    leanh::lean_dec(v___y_1919_);
    leanh::lean_dec_ref(v___y_1918_);
    leanh::lean_dec(v___y_1917_);
    leanh::lean_dec_ref(v___y_1916_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(
    mut v_e_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_unused_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1927_ = l_Lean_Expr_hasMVar(v_e_1924_);
                if v___x_1927_ == 0 {
                    v___x_1928_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1928_, 0, v_e_1924_);
                    return v___x_1928_;
                } else {
                    v___x_1929_ = lean_st_ref_get(v___y_1925_);
                    v_mctx_1930_ = leanh::lean_ctor_get(v___x_1929_, 0);
                    leanh::lean_inc_ref(v_mctx_1930_);
                    leanh::lean_dec(v___x_1929_);
                    v___x_1931_ = l_Lean_instantiateMVarsCore(v_mctx_1930_, v_e_1924_);
                    v_fst_1932_ = leanh::lean_ctor_get(v___x_1931_, 0);
                    leanh::lean_inc(v_fst_1932_);
                    v_snd_1933_ = leanh::lean_ctor_get(v___x_1931_, 1);
                    leanh::lean_inc(v_snd_1933_);
                    leanh::lean_dec_ref(v___x_1931_);
                    v___x_1934_ = lean_st_ref_take(v___y_1925_);
                    v_cache_1935_ = leanh::lean_ctor_get(v___x_1934_, 1);
                    v_zetaDeltaFVarIds_1936_ = leanh::lean_ctor_get(v___x_1934_, 2);
                    v_postponed_1937_ = leanh::lean_ctor_get(v___x_1934_, 3);
                    v_diag_1938_ = leanh::lean_ctor_get(v___x_1934_, 4);
                    v_isSharedCheck_1947_ = (!leanh::lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v_unused_1948_ = leanh::lean_ctor_get(v___x_1934_, 0);
                        leanh::lean_dec(v_unused_1948_);
                        v___x_1940_ = v___x_1934_;
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1938_);
                        leanh::lean_inc(v_postponed_1937_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1936_);
                        leanh::lean_inc(v_cache_1935_);
                        leanh::lean_dec(v___x_1934_);
                        v___x_1940_ = leanh::lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1941_ == 0 {
                    leanh::lean_ctor_set(v___x_1940_, 0, v_snd_1933_);
                    v___x_1943_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_snd_1933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_cache_1935_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1946_,
                        2,
                        v_zetaDeltaFVarIds_1936_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_postponed_1937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_diag_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1944_ = lean_st_ref_set(v___y_1925_, v___x_1943_);
                v___x_1945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1945_, 0, v_fst_1932_);
                return v___x_1945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(
    mut v_e_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1949_, v___y_1950_);
    leanh::lean_dec(v___y_1950_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(
    mut v_e_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1953_, v___y_1957_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(
    mut v_e_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(v_e_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    leanh::lean_dec(v___y_1968_);
    leanh::lean_dec_ref(v___y_1967_);
    leanh::lean_dec(v___y_1966_);
    leanh::lean_dec_ref(v___y_1965_);
    leanh::lean_dec(v___y_1964_);
    leanh::lean_dec_ref(v___y_1963_);
    return v_res_1970_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(
    mut v_msgData_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = lean_st_ref_get(v___y_1975_);
    v_env_1978_ = leanh::lean_ctor_get(v___x_1977_, 0);
    leanh::lean_inc_ref(v_env_1978_);
    leanh::lean_dec(v___x_1977_);
    v___x_1979_ = lean_st_ref_get(v___y_1973_);
    v_mctx_1980_ = leanh::lean_ctor_get(v___x_1979_, 0);
    leanh::lean_inc_ref(v_mctx_1980_);
    leanh::lean_dec(v___x_1979_);
    v_lctx_1981_ = leanh::lean_ctor_get(v___y_1972_, 2);
    v_options_1982_ = leanh::lean_ctor_get(v___y_1974_, 2);
    leanh::lean_inc_ref(v_options_1982_);
    leanh::lean_inc_ref(v_lctx_1981_);
    v___x_1983_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1983_, 0, v_env_1978_);
    leanh::lean_ctor_set(v___x_1983_, 1, v_mctx_1980_);
    leanh::lean_ctor_set(v___x_1983_, 2, v_lctx_1981_);
    leanh::lean_ctor_set(v___x_1983_, 3, v_options_1982_);
    v___x_1984_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1984_, 0, v___x_1983_);
    leanh::lean_ctor_set(v___x_1984_, 1, v_msgData_1971_);
    v___x_1985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(
    mut v_msgData_1986_: *mut leanh::LeanObject,
    mut v___y_1987_: *mut leanh::LeanObject,
    mut v___y_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msgData_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
    leanh::lean_dec(v___y_1990_);
    leanh::lean_dec_ref(v___y_1989_);
    leanh::lean_dec(v___y_1988_);
    leanh::lean_dec_ref(v___y_1987_);
    return v_res_1992_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1993_ = leanh::lean_box(1);
    v___x_1994_ = l_Lean_MessageData_ofFormat(v___x_1993_);
    return v___x_1994_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2;
    v___x_1999_ = l_Lean_MessageData_ofFormat(v___x_1998_);
    return v___x_1999_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(
    mut v_x_2000_: *mut leanh::LeanObject,
    mut v_x_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v_before_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_unused_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2001_) == 0 {
                    return v_x_2000_;
                } else {
                    v_head_2002_ = leanh::lean_ctor_get(v_x_2001_, 0);
                    v_tail_2003_ = leanh::lean_ctor_get(v_x_2001_, 1);
                    v_isSharedCheck_2025_ = (!leanh::lean_is_exclusive(v_x_2001_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2005_ = v_x_2001_;
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2003_);
                        leanh::lean_inc(v_head_2002_);
                        leanh::lean_dec(v_x_2001_);
                        v___x_2005_ = leanh::lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2007_ = leanh::lean_ctor_get(v_head_2002_, 0);
                v_isSharedCheck_2023_ = (!leanh::lean_is_exclusive(v_head_2002_)) as u8;
                if v_isSharedCheck_2023_ == 0 {
                    v_unused_2024_ = leanh::lean_ctor_get(v_head_2002_, 1);
                    leanh::lean_dec(v_unused_2024_);
                    v___x_2009_ = v_head_2002_;
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_2007_);
                    leanh::lean_dec(v_head_2002_);
                    v___x_2009_ = leanh::lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2011_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2010_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2009_, 7);
                    leanh::lean_ctor_set(v___x_2009_, 1, v___x_2011_);
                    leanh::lean_ctor_set(v___x_2009_, 0, v_x_2000_);
                    v___x_2013_ = v___x_2009_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_x_2000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3);
                if v_isShared_2006_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2005_, 7);
                    leanh::lean_ctor_set(v___x_2005_, 1, v___x_2014_);
                    leanh::lean_ctor_set(v___x_2005_, 0, v___x_2013_);
                    v___x_2016_ = v___x_2005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2014_);
                    v___x_2016_ = v_reuseFailAlloc_2021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2017_ = l_Lean_MessageData_ofSyntax(v_before_2007_);
                v___x_2018_ = l_Lean_indentD(v___x_2017_);
                v___x_2019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2019_, 0, v___x_2016_);
                leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
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
    mut v_opts_2026_: *mut leanh::LeanObject,
    mut v_opt_2027_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2028_ = leanh::lean_ctor_get(v_opt_2027_, 0);
    v_defValue_2029_ = leanh::lean_ctor_get(v_opt_2027_, 1);
    v_map_2030_ = leanh::lean_ctor_get(v_opts_2026_, 0);
    v___x_2031_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2030_,
            v_name_2028_,
        );
    if leanh::lean_obj_tag(v___x_2031_) == 0 {
        let mut v___x_2032_: u8 = 0;
        v___x_2032_ = (leanh::lean_unbox(v_defValue_2029_) as u8);
        return v___x_2032_;
    } else {
        let mut v_val_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2033_ = leanh::lean_ctor_get(v___x_2031_, 0);
        leanh::lean_inc(v_val_2033_);
        leanh::lean_dec_ref_known(v___x_2031_, 1);
        if leanh::lean_obj_tag(v_val_2033_) == 1 {
            let mut v_v_2034_: u8 = 0;
            v_v_2034_ = leanh::lean_ctor_get_uint8(v_val_2033_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2033_, 0);
            return v_v_2034_;
        } else {
            let mut v___x_2035_: u8 = 0;
            leanh::lean_dec(v_val_2033_);
            v___x_2035_ = (leanh::lean_unbox(v_defValue_2029_) as u8);
            return v___x_2035_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(
    mut v_opts_2036_: *mut leanh::LeanObject,
    mut v_opt_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2038_: u8 = 0;
    let mut v_r_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_opts_2036_, v_opt_2037_);
    leanh::lean_dec_ref(v_opt_2037_);
    leanh::lean_dec_ref(v_opts_2036_);
    v_r_2039_ = leanh::lean_box((v_res_2038_) as usize);
    return v_r_2039_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1;
    v___x_2044_ = l_Lean_MessageData_ofFormat(v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(
    mut v_msgData_2045_: *mut leanh::LeanObject,
    mut v_macroStack_2046_: *mut leanh::LeanObject,
    mut v___y_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2049_ = leanh::lean_ctor_get(v___y_2047_, 2);
                v___x_2050_ = l_Lean_Elab_pp_macroStack;
                v___x_2051_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_options_2049_, v___x_2050_);
                if v___x_2051_ == 0 {
                    leanh::lean_dec(v_macroStack_2046_);
                    v___x_2052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2052_, 0, v_msgData_2045_);
                    return v___x_2052_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_2046_) == 0 {
                        v___x_2053_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2053_, 0, v_msgData_2045_);
                        return v___x_2053_;
                    } else {
                        v_head_2054_ = leanh::lean_ctor_get(v_macroStack_2046_, 0);
                        leanh::lean_inc(v_head_2054_);
                        v_after_2055_ = leanh::lean_ctor_get(v_head_2054_, 1);
                        v_isSharedCheck_2070_ =
                            (!leanh::lean_is_exclusive(v_head_2054_)) as u8;
                        if v_isSharedCheck_2070_ == 0 {
                            v_unused_2071_ = leanh::lean_ctor_get(v_head_2054_, 0);
                            leanh::lean_dec(v_unused_2071_);
                            v___x_2057_ = v_head_2054_;
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_2055_);
                            leanh::lean_dec(v_head_2054_);
                            v___x_2057_ = leanh::lean_box(0);
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2059_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2058_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2057_, 7);
                    leanh::lean_ctor_set(v___x_2057_, 1, v___x_2059_);
                    leanh::lean_ctor_set(v___x_2057_, 0, v_msgData_2045_);
                    v___x_2061_ = v___x_2057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_msgData_2045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2059_);
                    v___x_2061_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2);
                v___x_2063_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                v___x_2064_ = l_Lean_MessageData_ofSyntax(v_after_2055_);
                v___x_2065_ = l_Lean_indentD(v___x_2064_);
                v_msgData_2066_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_2066_, 0, v___x_2063_);
                leanh::lean_ctor_set(v_msgData_2066_, 1, v___x_2065_);
                v___x_2067_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(v_msgData_2066_, v_macroStack_2046_);
                v___x_2068_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2068_, 0, v___x_2067_);
                return v___x_2068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(
    mut v_msgData_2072_: *mut leanh::LeanObject,
    mut v_macroStack_2073_: *mut leanh::LeanObject,
    mut v___y_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2072_, v_macroStack_2073_, v___y_2074_);
    leanh::lean_dec_ref(v___y_2074_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(
    mut v_msg_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2085_ = leanh::lean_ctor_get(v___y_2082_, 5);
                v___x_2086_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msg_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
                v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                leanh::lean_inc(v_a_2087_);
                leanh::lean_dec_ref(v___x_2086_);
                v_macroStack_2088_ = leanh::lean_ctor_get(v___y_2078_, 1);
                v___x_2089_ = l_Lean_Elab_getBetterRef(v_ref_2085_, v_macroStack_2088_);
                leanh::lean_inc(v_macroStack_2088_);
                v___x_2090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_a_2087_, v_macroStack_2088_, v___y_2082_);
                v_a_2091_ = leanh::lean_ctor_get(v___x_2090_, 0);
                v_isSharedCheck_2099_ = (!leanh::lean_is_exclusive(v___x_2090_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2093_ = v___x_2090_;
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2091_);
                    leanh::lean_dec(v___x_2090_);
                    v___x_2093_ = leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2095_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2095_, 0, v___x_2089_);
                leanh::lean_ctor_set(v___x_2095_, 1, v_a_2091_);
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2093_, 1);
                    leanh::lean_ctor_set(v___x_2093_, 0, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
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
    mut v_msg_2100_: *mut leanh::LeanObject,
    mut v___y_2101_: *mut leanh::LeanObject,
    mut v___y_2102_: *mut leanh::LeanObject,
    mut v___y_2103_: *mut leanh::LeanObject,
    mut v___y_2104_: *mut leanh::LeanObject,
    mut v___y_2105_: *mut leanh::LeanObject,
    mut v___y_2106_: *mut leanh::LeanObject,
    mut v___y_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    leanh::lean_dec(v___y_2106_);
    leanh::lean_dec_ref(v___y_2105_);
    leanh::lean_dec(v___y_2104_);
    leanh::lean_dec_ref(v___y_2103_);
    leanh::lean_dec(v___y_2102_);
    leanh::lean_dec_ref(v___y_2101_);
    return v_res_2108_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12;
    v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
    mut v_x_2148_: *mut leanh::LeanObject,
    mut v_a_2149_: *mut leanh::LeanObject,
    mut v_a_2150_: *mut leanh::LeanObject,
    mut v_a_2151_: *mut leanh::LeanObject,
    mut v_a_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_a_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2171_: u8 = 0;
    let mut v_cancelTk_x3f_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2173_: u8 = 0;
    let mut v_inheritedTraceOptions_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_reuseFailAlloc_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_a_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2156_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
                leanh::lean_inc(v_x_2148_);
                v___x_2157_ = l_Lean_Syntax_isOfKind(v_x_2148_, v___x_2156_);
                if v___x_2157_ == 0 {
                    leanh::lean_dec(v_x_2148_);
                    v___x_2158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
                    return v___x_2158_;
                } else {
                    v_fileName_2159_ = leanh::lean_ctor_get(v_a_2153_, 0);
                    v_fileMap_2160_ = leanh::lean_ctor_get(v_a_2153_, 1);
                    v_options_2161_ = leanh::lean_ctor_get(v_a_2153_, 2);
                    v_currRecDepth_2162_ = leanh::lean_ctor_get(v_a_2153_, 3);
                    v_maxRecDepth_2163_ = leanh::lean_ctor_get(v_a_2153_, 4);
                    v_ref_2164_ = leanh::lean_ctor_get(v_a_2153_, 5);
                    v_currNamespace_2165_ = leanh::lean_ctor_get(v_a_2153_, 6);
                    v_openDecls_2166_ = leanh::lean_ctor_get(v_a_2153_, 7);
                    v_initHeartbeats_2167_ = leanh::lean_ctor_get(v_a_2153_, 8);
                    v_maxHeartbeats_2168_ = leanh::lean_ctor_get(v_a_2153_, 9);
                    v_quotContext_2169_ = leanh::lean_ctor_get(v_a_2153_, 10);
                    v_currMacroScope_2170_ = leanh::lean_ctor_get(v_a_2153_, 11);
                    v_diag_2171_ = leanh::lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_2172_ = leanh::lean_ctor_get(v_a_2153_, 12);
                    v_suppressElabErrors_2173_ = leanh::lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_2174_ = leanh::lean_ctor_get(v_a_2153_, 13);
                    v___x_2175_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2176_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2175_);
                    v___x_2177_ = leanh::lean_box(0);
                    v_ref_2178_ = l_Lean_replaceRef(v___x_2176_, v_ref_2164_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_2174_);
                    leanh::lean_inc(v_cancelTk_x3f_2172_);
                    leanh::lean_inc(v_currMacroScope_2170_);
                    leanh::lean_inc(v_quotContext_2169_);
                    leanh::lean_inc(v_maxHeartbeats_2168_);
                    leanh::lean_inc(v_initHeartbeats_2167_);
                    leanh::lean_inc(v_openDecls_2166_);
                    leanh::lean_inc(v_currNamespace_2165_);
                    leanh::lean_inc(v_maxRecDepth_2163_);
                    leanh::lean_inc(v_currRecDepth_2162_);
                    leanh::lean_inc_ref(v_options_2161_);
                    leanh::lean_inc_ref(v_fileMap_2160_);
                    leanh::lean_inc_ref(v_fileName_2159_);
                    v___x_2179_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_2179_, 0, v_fileName_2159_);
                    leanh::lean_ctor_set(v___x_2179_, 1, v_fileMap_2160_);
                    leanh::lean_ctor_set(v___x_2179_, 2, v_options_2161_);
                    leanh::lean_ctor_set(v___x_2179_, 3, v_currRecDepth_2162_);
                    leanh::lean_ctor_set(v___x_2179_, 4, v_maxRecDepth_2163_);
                    leanh::lean_ctor_set(v___x_2179_, 5, v_ref_2178_);
                    leanh::lean_ctor_set(v___x_2179_, 6, v_currNamespace_2165_);
                    leanh::lean_ctor_set(v___x_2179_, 7, v_openDecls_2166_);
                    leanh::lean_ctor_set(v___x_2179_, 8, v_initHeartbeats_2167_);
                    leanh::lean_ctor_set(v___x_2179_, 9, v_maxHeartbeats_2168_);
                    leanh::lean_ctor_set(v___x_2179_, 10, v_quotContext_2169_);
                    leanh::lean_ctor_set(v___x_2179_, 11, v_currMacroScope_2170_);
                    leanh::lean_ctor_set(v___x_2179_, 12, v_cancelTk_x3f_2172_);
                    leanh::lean_ctor_set(v___x_2179_, 13, v_inheritedTraceOptions_2174_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_2171_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
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
                    if leanh::lean_obj_tag(v___x_2180_) == 0 {
                        v_a_2181_ = leanh::lean_ctor_get(v___x_2180_, 0);
                        leanh::lean_inc_n(v_a_2181_, 2);
                        leanh::lean_dec_ref_known(v___x_2180_, 1);
                        leanh::lean_inc(v_a_2154_);
                        leanh::lean_inc_ref(v___x_2179_);
                        leanh::lean_inc(v_a_2152_);
                        leanh::lean_inc_ref(v_a_2151_);
                        v___x_2182_ = lean_infer_type(
                            v_a_2181_,
                            v_a_2151_,
                            v_a_2152_,
                            v___x_2179_,
                            v_a_2154_,
                        );
                        if leanh::lean_obj_tag(v___x_2182_) == 0 {
                            v_a_2183_ = leanh::lean_ctor_get(v___x_2182_, 0);
                            leanh::lean_inc_n(v_a_2183_, 2);
                            leanh::lean_dec_ref_known(v___x_2182_, 1);
                            v___x_2184_ = l_Lean_Elab_Term_tryPostponeIfMVar(
                                v_a_2183_,
                                v_a_2149_,
                                v_a_2150_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if leanh::lean_obj_tag(v___x_2184_) == 0 {
                                leanh::lean_dec_ref_known(v___x_2184_, 1);
                                v___x_2185_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_a_2183_, v_a_2152_);
                                v_a_2186_ = leanh::lean_ctor_get(v___x_2185_, 0);
                                v_isSharedCheck_2319_ =
                                    (!leanh::lean_is_exclusive(v___x_2185_)) as u8;
                                if v_isSharedCheck_2319_ == 0 {
                                    v___x_2188_ = v___x_2185_;
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2186_);
                                    leanh::lean_dec(v___x_2185_);
                                    v___x_2188_ = leanh::lean_box(0);
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_2183_);
                                leanh::lean_dec(v_a_2181_);
                                leanh::lean_dec_ref_known(v___x_2179_, 14);
                                leanh::lean_dec(v_x_2148_);
                                v_a_2320_ = leanh::lean_ctor_get(v___x_2184_, 0);
                                v_isSharedCheck_2327_ =
                                    (!leanh::lean_is_exclusive(v___x_2184_)) as u8;
                                if v_isSharedCheck_2327_ == 0 {
                                    v___x_2322_ = v___x_2184_;
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2320_);
                                    leanh::lean_dec(v___x_2184_);
                                    v___x_2322_ = leanh::lean_box(0);
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2181_);
                            leanh::lean_dec_ref_known(v___x_2179_, 14);
                            leanh::lean_dec(v_x_2148_);
                            return v___x_2182_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2179_, 14);
                        leanh::lean_dec(v_x_2148_);
                        return v___x_2180_;
                    }
                }
            }
            1 => {
                v___x_2190_ = leanh::lean_unsigned_to_nat(1);
                v___x_2191_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2190_);
                v___x_2192_ = leanh::lean_unsigned_to_nat(5);
                v___x_2193_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2192_);
                leanh::lean_dec(v_x_2148_);
                v___x_2254_ = l_Lean_Expr_consumeMData(v_a_2186_);
                if leanh::lean_obj_tag(v___x_2254_) == 5 {
                    v_fn_2255_ = leanh::lean_ctor_get(v___x_2254_, 0);
                    leanh::lean_inc_ref(v_fn_2255_);
                    v_arg_2256_ = leanh::lean_ctor_get(v___x_2254_, 1);
                    leanh::lean_inc_ref_n(v_arg_2256_, 2);
                    leanh::lean_dec_ref_known(v___x_2254_, 2);
                    v___x_2257_ = l_Lean_Meta_getLevel(
                        v_arg_2256_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    if leanh::lean_obj_tag(v___x_2257_) == 0 {
                        v_a_2258_ = leanh::lean_ctor_get(v___x_2257_, 0);
                        leanh::lean_inc(v_a_2258_);
                        leanh::lean_dec_ref_known(v___x_2257_, 1);
                        v___x_2259_ = l_Lean_Level_dec(v_a_2258_);
                        leanh::lean_dec(v_a_2258_);
                        if leanh::lean_obj_tag(v___x_2259_) == 1 {
                            v_val_2260_ = leanh::lean_ctor_get(v___x_2259_, 0);
                            leanh::lean_inc(v_val_2260_);
                            leanh::lean_dec_ref_known(v___x_2259_, 1);
                            leanh::lean_inc(v_a_2186_);
                            v___x_2261_ = l_Lean_Meta_getLevel(
                                v_a_2186_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if leanh::lean_obj_tag(v___x_2261_) == 0 {
                                v_a_2262_ = leanh::lean_ctor_get(v___x_2261_, 0);
                                leanh::lean_inc(v_a_2262_);
                                leanh::lean_dec_ref_known(v___x_2261_, 1);
                                v___x_2263_ = l_Lean_Level_dec(v_a_2262_);
                                leanh::lean_dec(v_a_2262_);
                                if leanh::lean_obj_tag(v___x_2263_) == 1 {
                                    leanh::lean_dec(v_a_2186_);
                                    v_val_2264_ = leanh::lean_ctor_get(v___x_2263_, 0);
                                    v_isSharedCheck_2286_ =
                                        (!leanh::lean_is_exclusive(v___x_2263_)) as u8;
                                    if v_isSharedCheck_2286_ == 0 {
                                        v___x_2266_ = v___x_2263_;
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_2264_);
                                        leanh::lean_dec(v___x_2263_);
                                        v___x_2266_ = leanh::lean_box(0);
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_2263_);
                                    leanh::lean_dec(v_val_2260_);
                                    leanh::lean_dec_ref(v_arg_2256_);
                                    leanh::lean_dec_ref(v_fn_2255_);
                                    leanh::lean_dec(v___x_2193_);
                                    leanh::lean_dec(v___x_2191_);
                                    leanh::lean_del_object(v___x_2188_);
                                    leanh::lean_dec(v_a_2181_);
                                    v___x_2287_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                                    v___x_2288_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                                    v___x_2289_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_2289_, 0, v___x_2287_);
                                    leanh::lean_ctor_set(v___x_2289_, 1, v___x_2288_);
                                    v___x_2290_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2289_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                                    leanh::lean_dec_ref_known(v___x_2179_, 14);
                                    v___y_2245_ = v___x_2290_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_2260_);
                                leanh::lean_dec_ref(v_arg_2256_);
                                leanh::lean_dec_ref(v_fn_2255_);
                                leanh::lean_dec(v___x_2193_);
                                leanh::lean_dec(v___x_2191_);
                                leanh::lean_del_object(v___x_2188_);
                                leanh::lean_dec(v_a_2186_);
                                leanh::lean_dec(v_a_2181_);
                                leanh::lean_dec_ref_known(v___x_2179_, 14);
                                v_a_2291_ = leanh::lean_ctor_get(v___x_2261_, 0);
                                v_isSharedCheck_2298_ =
                                    (!leanh::lean_is_exclusive(v___x_2261_)) as u8;
                                if v_isSharedCheck_2298_ == 0 {
                                    v___x_2293_ = v___x_2261_;
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2291_);
                                    leanh::lean_dec(v___x_2261_);
                                    v___x_2293_ = leanh::lean_box(0);
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2259_);
                            leanh::lean_dec_ref(v_arg_2256_);
                            leanh::lean_dec_ref(v_fn_2255_);
                            leanh::lean_dec(v___x_2193_);
                            leanh::lean_dec(v___x_2191_);
                            leanh::lean_del_object(v___x_2188_);
                            leanh::lean_dec(v_a_2181_);
                            v___x_2299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                            v___x_2300_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                            v___x_2301_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_2301_, 0, v___x_2299_);
                            leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                            v___x_2302_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2301_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                            leanh::lean_dec_ref_known(v___x_2179_, 14);
                            v___y_2245_ = v___x_2302_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_2256_);
                        leanh::lean_dec_ref(v_fn_2255_);
                        leanh::lean_dec(v___x_2193_);
                        leanh::lean_dec(v___x_2191_);
                        leanh::lean_del_object(v___x_2188_);
                        leanh::lean_dec(v_a_2186_);
                        leanh::lean_dec(v_a_2181_);
                        leanh::lean_dec_ref_known(v___x_2179_, 14);
                        v_a_2303_ = leanh::lean_ctor_get(v___x_2257_, 0);
                        v_isSharedCheck_2310_ =
                            (!leanh::lean_is_exclusive(v___x_2257_)) as u8;
                        if v_isSharedCheck_2310_ == 0 {
                            v___x_2305_ = v___x_2257_;
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2303_);
                            leanh::lean_dec(v___x_2257_);
                            v___x_2305_ = leanh::lean_box(0);
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2254_);
                    leanh::lean_dec(v___x_2193_);
                    leanh::lean_dec(v___x_2191_);
                    leanh::lean_del_object(v___x_2188_);
                    v___x_2311_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15);
                    v___x_2312_ = l_Lean_MessageData_ofExpr(v_a_2181_);
                    v___x_2313_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2313_, 0, v___x_2311_);
                    leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                    v___x_2314_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17);
                    v___x_2315_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                    v___x_2317_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2317_, 0, v___x_2315_);
                    leanh::lean_ctor_set(v___x_2317_, 1, v___x_2316_);
                    v___x_2318_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2317_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                    leanh::lean_dec_ref_known(v___x_2179_, 14);
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
                leanh::lean_inc_n(v___x_2203_, 2);
                v___x_2206_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2206_, 0, v___x_2203_);
                leanh::lean_ctor_set(v___x_2206_, 1, v___x_2205_);
                v___x_2207_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_2208_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2208_, 0, v___x_2203_);
                leanh::lean_ctor_set(v___x_2208_, 1, v___x_2207_);
                v___x_2209_ = l_Lean_Syntax_node3(
                    v___x_2203_,
                    v___x_2204_,
                    v___x_2206_,
                    v___x_2191_,
                    v___x_2208_,
                );
                v___x_2210_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4;
                v___x_2211_ = leanh::lean_box(0);
                leanh::lean_inc(v_fst_2195_);
                v___x_2212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2212_, 0, v_fst_2195_);
                leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
                leanh::lean_inc_ref(v___x_2212_);
                v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
                leanh::lean_inc_ref(v_fst_2199_);
                v___x_2214_ = l_Lean_Expr_app___override(v___x_2213_, v_fst_2199_);
                if v_isShared_2189_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2188_, 1);
                    leanh::lean_ctor_set(v___x_2188_, 0, v___x_2214_);
                    v___x_2216_ = v___x_2188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2214_);
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
                if leanh::lean_obj_tag(v___x_2217_) == 0 {
                    v_a_2218_ = leanh::lean_ctor_get(v___x_2217_, 0);
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v___x_2217_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2220_ = v___x_2217_;
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2218_);
                        leanh::lean_dec(v___x_2217_);
                        v___x_2220_ = leanh::lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2212_, 2);
                    leanh::lean_dec_ref(v_snd_2201_);
                    leanh::lean_dec_ref(v_fst_2200_);
                    leanh::lean_dec_ref(v_fst_2199_);
                    leanh::lean_dec_ref(v_fst_2198_);
                    leanh::lean_dec_ref(v_fst_2197_);
                    leanh::lean_dec(v_fst_2196_);
                    leanh::lean_dec(v_fst_2195_);
                    leanh::lean_dec(v___x_2193_);
                    return v___x_2217_;
                }
            }
            4 => {
                v___x_2222_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5;
                v___x_2223_ = l_Lean_mkConst(v___x_2222_, v___x_2212_);
                leanh::lean_inc_ref(v_fst_2199_);
                leanh::lean_inc_ref(v_fst_2198_);
                v___x_2224_ = l_Lean_mkAppB(v___x_2223_, v_fst_2198_, v_fst_2199_);
                if v_isShared_2221_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2220_, 1);
                    leanh::lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                    v___x_2226_ = v___x_2220_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2224_);
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
                if leanh::lean_obj_tag(v___x_2227_) == 0 {
                    v_a_2228_ = leanh::lean_ctor_get(v___x_2227_, 0);
                    v_isSharedCheck_2240_ = (!leanh::lean_is_exclusive(v___x_2227_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v___x_2230_ = v___x_2227_;
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2228_);
                        leanh::lean_dec(v___x_2227_);
                        v___x_2230_ = leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2218_);
                    leanh::lean_dec_ref(v_snd_2201_);
                    leanh::lean_dec_ref(v_fst_2200_);
                    leanh::lean_dec_ref(v_fst_2199_);
                    leanh::lean_dec_ref(v_fst_2198_);
                    leanh::lean_dec_ref(v_fst_2197_);
                    leanh::lean_dec(v_fst_2196_);
                    leanh::lean_dec(v_fst_2195_);
                    return v___x_2227_;
                }
            }
            6 => {
                v___x_2232_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7;
                v___x_2233_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2233_, 0, v_fst_2196_);
                leanh::lean_ctor_set(v___x_2233_, 1, v___x_2211_);
                v___x_2234_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2234_, 0, v_fst_2195_);
                leanh::lean_ctor_set(v___x_2234_, 1, v___x_2233_);
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
                    leanh::lean_ctor_set(v___x_2230_, 0, v___x_2236_);
                    v___x_2238_ = v___x_2230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2239_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2238_;
            }
            8 => {
                v_a_2246_ = leanh::lean_ctor_get(v___y_2245_, 0);
                v_isSharedCheck_2253_ = (!leanh::lean_is_exclusive(v___y_2245_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v___x_2248_ = v___y_2245_;
                    v_isShared_2249_ = v_isSharedCheck_2253_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2246_);
                    leanh::lean_dec(v___y_2245_);
                    v___x_2248_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2252_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
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
                v___x_2269_ = leanh::lean_box(0);
                leanh::lean_inc(v_val_2260_);
                v___x_2270_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2270_, 0, v_val_2260_);
                leanh::lean_ctor_set(v___x_2270_, 1, v___x_2269_);
                v___x_2271_ = l_Lean_mkConst(v___x_2268_, v___x_2270_);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2266_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2285_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2274_ = 0;
                v___x_2275_ = leanh::lean_box(0);
                v___x_2276_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_2273_,
                    v___x_2274_,
                    v___x_2275_,
                    v_a_2151_,
                    v_a_2152_,
                    v___x_2179_,
                    v_a_2154_,
                );
                if leanh::lean_obj_tag(v___x_2276_) == 0 {
                    v_a_2277_ = leanh::lean_ctor_get(v___x_2276_, 0);
                    leanh::lean_inc_n(v_a_2277_, 2);
                    leanh::lean_dec_ref_known(v___x_2276_, 1);
                    v___x_2278_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11;
                    leanh::lean_inc(v_val_2264_);
                    v___x_2279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2279_, 0, v_val_2264_);
                    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2269_);
                    leanh::lean_inc(v_val_2260_);
                    v___x_2280_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2280_, 0, v_val_2260_);
                    leanh::lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                    v___x_2281_ = l_Lean_mkConst(v___x_2278_, v___x_2280_);
                    leanh::lean_inc_ref(v_fn_2255_);
                    v___x_2282_ = l_Lean_mkAppB(v___x_2281_, v_fn_2255_, v_a_2277_);
                    v___x_2283_ = l_Lean_Meta_synthInstance(
                        v___x_2282_,
                        v___x_2177_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    leanh::lean_dec_ref_known(v___x_2179_, 14);
                    if leanh::lean_obj_tag(v___x_2283_) == 0 {
                        v_a_2284_ = leanh::lean_ctor_get(v___x_2283_, 0);
                        leanh::lean_inc(v_a_2284_);
                        leanh::lean_dec_ref_known(v___x_2283_, 1);
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
                        leanh::lean_dec(v_a_2277_);
                        leanh::lean_dec(v_val_2264_);
                        leanh::lean_dec(v_val_2260_);
                        leanh::lean_dec_ref(v_arg_2256_);
                        leanh::lean_dec_ref(v_fn_2255_);
                        leanh::lean_dec(v___x_2193_);
                        leanh::lean_dec(v___x_2191_);
                        leanh::lean_del_object(v___x_2188_);
                        leanh::lean_dec(v_a_2181_);
                        return v___x_2283_;
                    }
                } else {
                    leanh::lean_dec(v_val_2264_);
                    leanh::lean_dec(v_val_2260_);
                    leanh::lean_dec_ref(v_arg_2256_);
                    leanh::lean_dec_ref(v_fn_2255_);
                    leanh::lean_dec(v___x_2193_);
                    leanh::lean_dec(v___x_2191_);
                    leanh::lean_del_object(v___x_2188_);
                    leanh::lean_dec(v_a_2181_);
                    leanh::lean_dec_ref_known(v___x_2179_, 14);
                    return v___x_2276_;
                }
            }
            13 => {
                if v_isShared_2294_ == 0 {
                    v___x_2296_ = v___x_2293_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
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
                    v_reuseFailAlloc_2309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
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
                    v_reuseFailAlloc_2326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
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
    mut v_x_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v_a_2330_: *mut leanh::LeanObject,
    mut v_a_2331_: *mut leanh::LeanObject,
    mut v_a_2332_: *mut leanh::LeanObject,
    mut v_a_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2336_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_,
    );
    leanh::lean_dec(v_a_2334_);
    leanh::lean_dec_ref(v_a_2333_);
    leanh::lean_dec(v_a_2332_);
    leanh::lean_dec_ref(v_a_2331_);
    leanh::lean_dec(v_a_2330_);
    leanh::lean_dec_ref(v_a_2329_);
    return v_res_2336_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
    mut v_x_2337_: *mut leanh::LeanObject,
    mut v_x_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_a_2340_: *mut leanh::LeanObject,
    mut v_a_2341_: *mut leanh::LeanObject,
    mut v_a_2342_: *mut leanh::LeanObject,
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_a_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2346_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2337_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_,
    );
    return v___x_2346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(
    mut v_x_2347_: *mut leanh::LeanObject,
    mut v_x_2348_: *mut leanh::LeanObject,
    mut v_a_2349_: *mut leanh::LeanObject,
    mut v_a_2350_: *mut leanh::LeanObject,
    mut v_a_2351_: *mut leanh::LeanObject,
    mut v_a_2352_: *mut leanh::LeanObject,
    mut v_a_2353_: *mut leanh::LeanObject,
    mut v_a_2354_: *mut leanh::LeanObject,
    mut v_a_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2356_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
        v_x_2347_, v_x_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_,
    );
    leanh::lean_dec(v_a_2354_);
    leanh::lean_dec_ref(v_a_2353_);
    leanh::lean_dec(v_a_2352_);
    leanh::lean_dec_ref(v_a_2351_);
    leanh::lean_dec(v_a_2350_);
    leanh::lean_dec_ref(v_a_2349_);
    leanh::lean_dec(v_x_2348_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(
    mut v_00_u03b1_2357_: *mut leanh::LeanObject,
    mut v_msg_2358_: *mut leanh::LeanObject,
    mut v___y_2359_: *mut leanh::LeanObject,
    mut v___y_2360_: *mut leanh::LeanObject,
    mut v___y_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(
    mut v_00_u03b1_2367_: *mut leanh::LeanObject,
    mut v_msg_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v___y_2370_: *mut leanh::LeanObject,
    mut v___y_2371_: *mut leanh::LeanObject,
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v___y_2373_: *mut leanh::LeanObject,
    mut v___y_2374_: *mut leanh::LeanObject,
    mut v___y_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(v_00_u03b1_2367_, v_msg_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
    leanh::lean_dec(v___y_2374_);
    leanh::lean_dec_ref(v___y_2373_);
    leanh::lean_dec(v___y_2372_);
    leanh::lean_dec_ref(v___y_2371_);
    leanh::lean_dec(v___y_2370_);
    leanh::lean_dec_ref(v___y_2369_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(
    mut v_msgData_2377_: *mut leanh::LeanObject,
    mut v_macroStack_2378_: *mut leanh::LeanObject,
    mut v___y_2379_: *mut leanh::LeanObject,
    mut v___y_2380_: *mut leanh::LeanObject,
    mut v___y_2381_: *mut leanh::LeanObject,
    mut v___y_2382_: *mut leanh::LeanObject,
    mut v___y_2383_: *mut leanh::LeanObject,
    mut v___y_2384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2377_, v_macroStack_2378_, v___y_2383_);
    return v___x_2386_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(
    mut v_msgData_2387_: *mut leanh::LeanObject,
    mut v_macroStack_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
    mut v___y_2395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(v_msgData_2387_, v_macroStack_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
    leanh::lean_dec(v___y_2394_);
    leanh::lean_dec_ref(v___y_2393_);
    leanh::lean_dec(v___y_2392_);
    leanh::lean_dec_ref(v___y_2391_);
    leanh::lean_dec(v___y_2390_);
    leanh::lean_dec_ref(v___y_2389_);
    return v_res_2396_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1()
-> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_2403_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
    v___x_2404_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1;
    v___x_2405_ = leanh::lean_alloc_closure(
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
    mut v_a_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    return v_res_2408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Syntax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Syntax(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Syntax(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_Triple_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
}