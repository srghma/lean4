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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 101, 114, 109, 83, 112, 114, 101, 100, 40, 95, 41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__2_value) as *mut LeanObject,13979102795498516556 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__7_value) as *mut LeanObject,7932075773091973500 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 101, 114, 109, 73, 102, 84, 104, 101, 110, 69, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__9_value) as *mut LeanObject,14296711813398647265 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [102, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11_value) as *mut LeanObject,7043493786777132025 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__13_value) as *mut LeanObject,5346268661279150583 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__15_value) as *mut LeanObject,7306243862518720553 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__17_value) as *mut LeanObject,9871775667037945883 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20_value) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 80, 114, 101, 100, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__22_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__23_value) as *mut LeanObject,611622866940524098 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__24_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__26_value) as *mut LeanObject,300274991653824376 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__27_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__29_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 99, 114, 111, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__31_value) as *mut LeanObject,18105168627502861736 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__32_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__34_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__35_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__33_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__36_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__30_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__37_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__28_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__38_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__25_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__39_value) as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__42_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut LeanObject;
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__45_value) as *mut LeanObject,16077784126176397009 as *mut LeanObject] };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46_value) as *mut LeanObject;
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 102, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 101, 110, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50_value) as *mut LeanObject;
pub static l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [101, 108, 115, 101, 0]};
static mut l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51: *mut LeanObject = core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PrettyPrinter_Delaborator_delab___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__1_value) as *mut LeanObject,12966880221525079621 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 111, 115, 116, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut LeanObject,11553573755926099728 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 10, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__7_value) as *mut LeanObject,8463861479368259073 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 111, 117, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__9_value) as *mut LeanObject,2214559063752339918 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 135, 147, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__4_value) as *mut LeanObject,3676176009791887579 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__1_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__4_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__4_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__6_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,14659826576719934041 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__9_value) as *mut LeanObject,6004524207281992990 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__10_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9130596894474051559 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,7722122208264906652 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,14847410795624973596 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 78, 111, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__14_value) as *mut LeanObject,17122680503757600671 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut LeanObject,2940964116523157683 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 11, m_data: [116, 101, 114, 109, 95, 226, 135, 147, 63, 95, 61, 62, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__3_value) as *mut LeanObject,5101830612129297492 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 2, m_data: [226, 135, 147, 63, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut LeanObject,13156709450692335107 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__0_value) as *mut LeanObject,7425120582457359416 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [117, 110, 101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 67, 111, 110, 100, 77, 97, 121, 84, 104, 114, 111, 119, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__1_value) as *mut LeanObject,4163951709596513047 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__0_value) as *mut LeanObject,13939969460734853986 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 114, 101, 100, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [65, 115, 115, 101, 114, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__3_value) as *mut LeanObject,4155561471746556359 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__3_value) as *mut LeanObject,3393990892394863740 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__6_value) as *mut LeanObject,11963640885769744415 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__8_value) as *mut LeanObject,6471916472876379905 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__9_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 80, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value
) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__10_value) as *mut LeanObject,6757038018435374033 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [87, 114, 111, 110, 103, 32, 108, 101, 118, 101, 108, 32, 48, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 121, 112, 101, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 121, 112, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 58, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 84, 114, 105, 112, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__0_value) as *mut LeanObject,4122983324971754373 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21()
-> *mut LeanObject {
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1247_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__20;
    v___x_1248_ = l_String_toRawSubstring_x27(v___x_1247_);
    return v___x_1248_;
}
pub unsafe fn _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47()
-> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Array_mkArray0(lean_box(0));
    return v___x_1305_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(
    mut v_x_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: u8 = 0;
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: u8 = 0;
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v_ref_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v_ref_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1417_: u8 = 0;
    let mut v_ref_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_P_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1452_: u8 = 0;
    let mut v_ref_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1471_: u8 = 0;
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1313_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__3;
                lean_inc(v_x_1310_);
                v___x_1314_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1313_);
                if v___x_1314_ == 0 {
                    v___x_1315_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__8;
                    lean_inc(v_x_1310_);
                    v___x_1316_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1315_);
                    if v___x_1316_ == 0 {
                        v___x_1317_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__10;
                        lean_inc(v_x_1310_);
                        v___x_1318_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1317_);
                        if v___x_1318_ == 0 {
                            v___x_1319_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__11;
                            v___x_1320_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__12;
                            lean_inc(v_x_1310_);
                            v___x_1321_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1320_);
                            if v___x_1321_ == 0 {
                                v___x_1322_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__14;
                                lean_inc(v_x_1310_);
                                v___x_1323_ = l_Lean_Syntax_isOfKind(v_x_1310_, v___x_1322_);
                                if v___x_1323_ == 0 {
                                    v___x_1324_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1324_, 0, v_x_1310_);
                                    return v___x_1324_;
                                } else {
                                    v___x_1325_ = lean_unsigned_to_nat(0);
                                    v___x_1326_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1325_);
                                    v___x_1327_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                                    lean_inc(v___x_1326_);
                                    v___x_1328_ = l_Lean_Syntax_isOfKind(v___x_1326_, v___x_1327_);
                                    if v___x_1328_ == 0 {
                                        lean_dec(v___x_1326_);
                                        v___x_1329_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1329_, 0, v_x_1310_);
                                        return v___x_1329_;
                                    } else {
                                        v___x_1330_ = lean_unsigned_to_nat(1);
                                        v___x_1331_ =
                                            l_Lean_Syntax_getArg(v___x_1326_, v___x_1330_);
                                        lean_dec(v___x_1326_);
                                        v___x_1332_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                                        lean_inc(v___x_1331_);
                                        v___x_1333_ =
                                            l_Lean_Syntax_isOfKind(v___x_1331_, v___x_1332_);
                                        if v___x_1333_ == 0 {
                                            lean_dec(v___x_1331_);
                                            v___x_1334_ = lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v___x_1334_, 0, v_x_1310_);
                                            return v___x_1334_;
                                        } else {
                                            v___x_1335_ =
                                                l_Lean_Syntax_getArg(v___x_1331_, v___x_1325_);
                                            lean_dec(v___x_1331_);
                                            v___x_1336_ = lean_box(0);
                                            v___x_1337_ = l_Lean_Syntax_matchesIdent(
                                                v___x_1335_,
                                                v___x_1336_,
                                            );
                                            lean_dec(v___x_1335_);
                                            if v___x_1337_ == 0 {
                                                v___x_1338_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v___x_1338_, 0, v_x_1310_);
                                                return v___x_1338_;
                                            } else {
                                                v___x_1339_ = lean_unsigned_to_nat(3);
                                                v___x_1340_ =
                                                    l_Lean_Syntax_getArg(v_x_1310_, v___x_1339_);
                                                lean_inc(v___x_1340_);
                                                v___x_1341_ = l_Lean_Syntax_matchesNull(
                                                    v___x_1340_,
                                                    v___x_1330_,
                                                );
                                                if v___x_1341_ == 0 {
                                                    lean_dec(v___x_1340_);
                                                    v___x_1342_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(v___x_1342_, 0, v_x_1310_);
                                                    return v___x_1342_;
                                                } else {
                                                    v_P_1343_ = l_Lean_Syntax_getArg(
                                                        v_x_1310_,
                                                        v___x_1330_,
                                                    );
                                                    lean_dec(v_x_1310_);
                                                    v___x_1344_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1343_, v___y_1311_);
                                                    if lean_obj_tag(v___x_1344_) == 0 {
                                                        v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
                                                        v_isSharedCheck_1372_ =
                                                            (!lean_is_exclusive(v___x_1344_)) as u8;
                                                        if v_isSharedCheck_1372_ == 0 {
                                                            v___x_1347_ = v___x_1344_;
                                                            v_isShared_1348_ =
                                                                v_isSharedCheck_1372_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_1345_);
                                                            lean_dec(v___x_1344_);
                                                            v___x_1347_ = lean_box(0);
                                                            v_isShared_1348_ =
                                                                v_isSharedCheck_1372_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v___x_1340_);
                                                        return v___x_1344_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_1373_ = lean_unsigned_to_nat(1);
                                v___x_1374_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1373_);
                                v___x_1375_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                                lean_inc(v___x_1374_);
                                v___x_1376_ = l_Lean_Syntax_isOfKind(v___x_1374_, v___x_1375_);
                                if v___x_1376_ == 0 {
                                    lean_dec(v___x_1374_);
                                    v___x_1377_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1377_, 0, v_x_1310_);
                                    return v___x_1377_;
                                } else {
                                    v___x_1378_ = lean_unsigned_to_nat(0);
                                    v___x_1379_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1373_);
                                    v___x_1380_ =
                                        l_Lean_Syntax_matchesNull(v___x_1379_, v___x_1378_);
                                    if v___x_1380_ == 0 {
                                        lean_dec(v___x_1374_);
                                        v___x_1381_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_1381_, 0, v_x_1310_);
                                        return v___x_1381_;
                                    } else {
                                        lean_dec(v_x_1310_);
                                        v___x_1382_ = lean_unsigned_to_nat(3);
                                        v_b_1383_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1382_);
                                        v___x_1384_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_b_1383_, v___y_1311_);
                                        if lean_obj_tag(v___x_1384_) == 0 {
                                            v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
                                            v_isSharedCheck_1406_ =
                                                (!lean_is_exclusive(v___x_1384_)) as u8;
                                            if v_isSharedCheck_1406_ == 0 {
                                                v___x_1387_ = v___x_1384_;
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_1385_);
                                                lean_dec(v___x_1384_);
                                                v___x_1387_ = lean_box(0);
                                                v_isShared_1388_ = v_isSharedCheck_1406_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v___x_1374_);
                                            return v___x_1384_;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_1407_ = lean_unsigned_to_nat(3);
                            v_t_1408_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1407_);
                            v___x_1409_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_t_1408_, v___y_1311_);
                            if lean_obj_tag(v___x_1409_) == 0 {
                                v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
                                lean_inc(v_a_1410_);
                                lean_dec_ref_known(v___x_1409_, 1);
                                v___x_1411_ = lean_unsigned_to_nat(5);
                                v_e_1412_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1411_);
                                v___x_1413_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_e_1412_, v___y_1311_);
                                if lean_obj_tag(v___x_1413_) == 0 {
                                    v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
                                    v_isSharedCheck_1432_ = (!lean_is_exclusive(v___x_1413_)) as u8;
                                    if v_isSharedCheck_1432_ == 0 {
                                        v___x_1416_ = v___x_1413_;
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1414_);
                                        lean_dec(v___x_1413_);
                                        v___x_1416_ = lean_box(0);
                                        v_isShared_1417_ = v_isSharedCheck_1432_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1410_);
                                    lean_dec(v_x_1310_);
                                    return v___x_1413_;
                                }
                            } else {
                                lean_dec(v_x_1310_);
                                return v___x_1409_;
                            }
                        }
                    } else {
                        v___x_1433_ = lean_unsigned_to_nat(0);
                        v___x_1434_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1433_);
                        v___x_1435_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__16;
                        lean_inc(v___x_1434_);
                        v___x_1436_ = l_Lean_Syntax_isOfKind(v___x_1434_, v___x_1435_);
                        if v___x_1436_ == 0 {
                            lean_dec(v___x_1434_);
                            v___x_1437_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1437_, 0, v_x_1310_);
                            return v___x_1437_;
                        } else {
                            v___x_1438_ = lean_unsigned_to_nat(1);
                            v___x_1439_ = l_Lean_Syntax_getArg(v___x_1434_, v___x_1438_);
                            lean_dec(v___x_1434_);
                            v___x_1440_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__18;
                            lean_inc(v___x_1439_);
                            v___x_1441_ = l_Lean_Syntax_isOfKind(v___x_1439_, v___x_1440_);
                            if v___x_1441_ == 0 {
                                lean_dec(v___x_1439_);
                                v___x_1442_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1442_, 0, v_x_1310_);
                                return v___x_1442_;
                            } else {
                                v___x_1443_ = l_Lean_Syntax_getArg(v___x_1439_, v___x_1433_);
                                lean_dec(v___x_1439_);
                                v___x_1444_ = lean_box(0);
                                v___x_1445_ = l_Lean_Syntax_matchesIdent(v___x_1443_, v___x_1444_);
                                lean_dec(v___x_1443_);
                                if v___x_1445_ == 0 {
                                    v___x_1446_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_1446_, 0, v_x_1310_);
                                    return v___x_1446_;
                                } else {
                                    v_P_1447_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1438_);
                                    lean_dec(v_x_1310_);
                                    v___x_1448_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_P_1447_, v___y_1311_);
                                    if lean_obj_tag(v___x_1448_) == 0 {
                                        v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
                                        v_isSharedCheck_1471_ =
                                            (!lean_is_exclusive(v___x_1448_)) as u8;
                                        if v_isSharedCheck_1471_ == 0 {
                                            v___x_1451_ = v___x_1448_;
                                            v_isShared_1452_ = v_isSharedCheck_1471_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1449_);
                                            lean_dec(v___x_1448_);
                                            v___x_1451_ = lean_box(0);
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
                    v___x_1472_ = lean_unsigned_to_nat(1);
                    v___x_1473_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1472_);
                    lean_dec(v_x_1310_);
                    v___x_1474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                    return v___x_1474_;
                }
            }
            1 => {
                v_ref_1349_ = lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1350_ = lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1351_ = lean_ctor_get(v___y_1311_, 11);
                v___x_1352_ = l_Lean_Syntax_getArg(v___x_1340_, v___x_1325_);
                lean_dec(v___x_1340_);
                v___x_1353_ = l_Lean_SourceInfo_fromRef(v_ref_1349_, v___x_1321_);
                v___x_1354_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                lean_inc_n(v___x_1353_, 7);
                v___x_1355_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1355_, 0, v___x_1353_);
                lean_ctor_set(v___x_1355_, 1, v___x_1354_);
                v___x_1356_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                lean_inc(v_currMacroScope_1351_);
                lean_inc(v_quotContext_1350_);
                v___x_1357_ =
                    l_Lean_addMacroScope(v_quotContext_1350_, v___x_1336_, v_currMacroScope_1351_);
                v___x_1358_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1359_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1359_, 0, v___x_1353_);
                lean_ctor_set(v___x_1359_, 1, v___x_1356_);
                lean_ctor_set(v___x_1359_, 2, v___x_1357_);
                lean_ctor_set(v___x_1359_, 3, v___x_1358_);
                v___x_1360_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1332_, v___x_1359_);
                v___x_1361_ =
                    l_Lean_Syntax_node2(v___x_1353_, v___x_1327_, v___x_1355_, v___x_1360_);
                v___x_1362_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__41;
                v___x_1363_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1363_, 0, v___x_1353_);
                lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                v___x_1364_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1365_ = l_Lean_Syntax_node1(v___x_1353_, v___x_1364_, v___x_1352_);
                v___x_1366_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1367_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1367_, 0, v___x_1353_);
                lean_ctor_set(v___x_1367_, 1, v___x_1366_);
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
                    lean_ctor_set(v___x_1347_, 0, v___x_1368_);
                    v___x_1370_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1370_;
            }
            3 => {
                v_ref_1389_ = lean_ctor_get(v___y_1311_, 5);
                v___x_1390_ = l_Lean_Syntax_getArg(v___x_1374_, v___x_1378_);
                lean_dec(v___x_1374_);
                v_xs_1391_ = l_Lean_Syntax_getArgs(v___x_1390_);
                lean_dec(v___x_1390_);
                v___x_1392_ = l_Lean_SourceInfo_fromRef(v_ref_1389_, v___x_1318_);
                lean_inc_n(v___x_1392_, 5);
                v___x_1393_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1393_, 0, v___x_1392_);
                lean_ctor_set(v___x_1393_, 1, v___x_1319_);
                v___x_1394_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1395_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                v___x_1396_ = l_Array_append___redArg(v___x_1395_, v_xs_1391_);
                lean_dec_ref(v_xs_1391_);
                v___x_1397_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1397_, 0, v___x_1392_);
                lean_ctor_set(v___x_1397_, 1, v___x_1394_);
                lean_ctor_set(v___x_1397_, 2, v___x_1396_);
                v___x_1398_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1398_, 0, v___x_1392_);
                lean_ctor_set(v___x_1398_, 1, v___x_1394_);
                lean_ctor_set(v___x_1398_, 2, v___x_1395_);
                v___x_1399_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1400_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1400_, 0, v___x_1392_);
                lean_ctor_set(v___x_1400_, 1, v___x_1399_);
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
                    lean_ctor_set(v___x_1387_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1404_;
            }
            5 => {
                v_ref_1418_ = lean_ctor_get(v___y_1311_, 5);
                v___x_1419_ = lean_unsigned_to_nat(1);
                v___x_1420_ = l_Lean_Syntax_getArg(v_x_1310_, v___x_1419_);
                lean_dec(v_x_1310_);
                v___x_1421_ = l_Lean_SourceInfo_fromRef(v_ref_1418_, v___x_1316_);
                v___x_1422_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__49;
                lean_inc_n(v___x_1421_, 3);
                v___x_1423_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1423_, 0, v___x_1421_);
                lean_ctor_set(v___x_1423_, 1, v___x_1422_);
                v___x_1424_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__50;
                v___x_1425_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1425_, 0, v___x_1421_);
                lean_ctor_set(v___x_1425_, 1, v___x_1424_);
                v___x_1426_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__51;
                v___x_1427_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1427_, 0, v___x_1421_);
                lean_ctor_set(v___x_1427_, 1, v___x_1426_);
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
                    lean_ctor_set(v___x_1416_, 0, v___x_1428_);
                    v___x_1430_ = v___x_1416_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1428_);
                    v___x_1430_ = v_reuseFailAlloc_1431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1430_;
            }
            7 => {
                v_ref_1453_ = lean_ctor_get(v___y_1311_, 5);
                v_quotContext_1454_ = lean_ctor_get(v___y_1311_, 10);
                v_currMacroScope_1455_ = lean_ctor_get(v___y_1311_, 11);
                v___x_1456_ = l_Lean_SourceInfo_fromRef(v_ref_1453_, v___x_1314_);
                v___x_1457_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__19;
                lean_inc_n(v___x_1456_, 5);
                v___x_1458_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1458_, 0, v___x_1456_);
                lean_ctor_set(v___x_1458_, 1, v___x_1457_);
                v___x_1459_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__21);
                lean_inc(v_currMacroScope_1455_);
                lean_inc(v_quotContext_1454_);
                v___x_1460_ =
                    l_Lean_addMacroScope(v_quotContext_1454_, v___x_1444_, v_currMacroScope_1455_);
                v___x_1461_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__40;
                v___x_1462_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_1462_, 0, v___x_1456_);
                lean_ctor_set(v___x_1462_, 1, v___x_1459_);
                lean_ctor_set(v___x_1462_, 2, v___x_1460_);
                lean_ctor_set(v___x_1462_, 3, v___x_1461_);
                v___x_1463_ = l_Lean_Syntax_node1(v___x_1456_, v___x_1440_, v___x_1462_);
                v___x_1464_ =
                    l_Lean_Syntax_node2(v___x_1456_, v___x_1435_, v___x_1458_, v___x_1463_);
                v___x_1465_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_1466_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1466_, 0, v___x_1456_);
                lean_ctor_set(v___x_1466_, 1, v___x_1465_);
                v___x_1467_ = l_Lean_Syntax_node3(
                    v___x_1456_,
                    v___x_1315_,
                    v___x_1464_,
                    v_a_1449_,
                    v___x_1466_,
                );
                if v_isShared_1452_ == 0 {
                    lean_ctor_set(v___x_1451_, 0, v___x_1467_);
                    v___x_1469_ = v___x_1451_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
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
    mut v_x_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1478_: *mut LeanObject = core::ptr::null_mut();
    v_res_1478_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1475_, v___y_1476_);
    lean_dec_ref(v___y_1476_);
    return v_res_1478_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(
    mut v_child_1479_: *mut LeanObject,
    mut v_childIdx_1480_: *mut LeanObject,
    mut v_x_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
    mut v___y_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subExpr_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_optionsPerPos_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inPattern_1493_: u8 = 0;
    let mut v_depth_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctxInitIndices_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v_subExpr_1489_ = lean_ctor_get(v___y_1482_, 3);
    v_optionsPerPos_1490_ = lean_ctor_get(v___y_1482_, 0);
    v_currNamespace_1491_ = lean_ctor_get(v___y_1482_, 1);
    v_openDecls_1492_ = lean_ctor_get(v___y_1482_, 2);
    v_inPattern_1493_ = lean_ctor_get_uint8(
        v___y_1482_,
        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
    );
    v_depth_1494_ = lean_ctor_get(v___y_1482_, 4);
    v_lctxInitIndices_1495_ = lean_ctor_get(v___y_1482_, 5);
    v_pos_1496_ = lean_ctor_get(v_subExpr_1489_, 1);
    v___x_1497_ = l_Lean_SubExpr_Pos_push(v_pos_1496_, v_childIdx_1480_);
    v___x_1498_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1498_, 0, v_child_1479_);
    lean_ctor_set(v___x_1498_, 1, v___x_1497_);
    lean_inc(v_lctxInitIndices_1495_);
    lean_inc(v_depth_1494_);
    lean_inc(v_openDecls_1492_);
    lean_inc(v_currNamespace_1491_);
    lean_inc(v_optionsPerPos_1490_);
    v___x_1499_ = lean_alloc_ctor(0, 6, (1) as u32);
    lean_ctor_set(v___x_1499_, 0, v_optionsPerPos_1490_);
    lean_ctor_set(v___x_1499_, 1, v_currNamespace_1491_);
    lean_ctor_set(v___x_1499_, 2, v_openDecls_1492_);
    lean_ctor_set(v___x_1499_, 3, v___x_1498_);
    lean_ctor_set(v___x_1499_, 4, v_depth_1494_);
    lean_ctor_set(v___x_1499_, 5, v_lctxInitIndices_1495_);
    lean_ctor_set_uint8(
        v___x_1499_,
        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
        v_inPattern_1493_,
    );
    lean_inc(v___y_1487_);
    lean_inc_ref(v___y_1486_);
    lean_inc(v___y_1485_);
    lean_inc_ref(v___y_1484_);
    lean_inc(v___y_1483_);
    v___x_1500_ = lean_apply_7(
        v_x_1481_,
        v___x_1499_,
        v___y_1483_,
        v___y_1484_,
        v___y_1485_,
        v___y_1486_,
        v___y_1487_,
        lean_box(0),
    );
    return v___x_1500_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg___boxed(
    mut v_child_1501_: *mut LeanObject,
    mut v_childIdx_1502_: *mut LeanObject,
    mut v_x_1503_: *mut LeanObject,
    mut v___y_1504_: *mut LeanObject,
    mut v___y_1505_: *mut LeanObject,
    mut v___y_1506_: *mut LeanObject,
    mut v___y_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1511_: *mut LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1501_, v_childIdx_1502_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
    lean_dec(v___y_1509_);
    lean_dec_ref(v___y_1508_);
    lean_dec(v___y_1507_);
    lean_dec_ref(v___y_1506_);
    lean_dec(v___y_1505_);
    lean_dec_ref(v___y_1504_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(
    mut v___y_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_subExpr_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v_subExpr_1514_ = lean_ctor_get(v___y_1512_, 3);
    v_expr_1515_ = lean_ctor_get(v_subExpr_1514_, 0);
    lean_inc_ref(v_expr_1515_);
    v___x_1516_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1516_, 0, v_expr_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg___boxed(
    mut v___y_1517_: *mut LeanObject,
    mut v___y_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1519_: *mut LeanObject = core::ptr::null_mut();
    v_res_1519_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1517_);
    lean_dec_ref(v___y_1517_);
    return v_res_1519_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(
    mut v_x_1520_: *mut LeanObject,
    mut v___y_1521_: *mut LeanObject,
    mut v___y_1522_: *mut LeanObject,
    mut v___y_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
    mut v___y_1526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1521_);
    v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
    lean_inc(v_a_1529_);
    lean_dec_ref(v___x_1528_);
    v___x_1530_ = l_Lean_Expr_appArg_x21(v_a_1529_);
    lean_dec(v_a_1529_);
    v___x_1531_ = lean_unsigned_to_nat(1);
    v___x_1532_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v___x_1530_, v___x_1531_, v_x_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
    return v___x_1532_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg___boxed(
    mut v_x_1533_: *mut LeanObject,
    mut v___y_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
    lean_dec(v___y_1539_);
    lean_dec_ref(v___y_1538_);
    lean_dec(v___y_1537_);
    lean_dec_ref(v___y_1536_);
    lean_dec(v___y_1535_);
    lean_dec_ref(v___y_1534_);
    return v_res_1541_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6()
-> *mut LeanObject {
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1556_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__5;
    v___x_1557_ = lean_mk_syntax_ident(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
    mut v_a_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
    mut v_a_1569_: *mut LeanObject,
    mut v_a_1570_: *mut LeanObject,
    mut v_a_1571_: *mut LeanObject,
    mut v_a_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    let mut v_ref_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: u8 = 0;
    let mut v_ref_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: u8 = 0;
    let mut v_ref_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v_ref_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_isSharedCheck_1647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1574_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1575_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1574_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_);
                if lean_obj_tag(v___x_1575_) == 0 {
                    v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
                    v_isSharedCheck_1647_ = (!lean_is_exclusive(v___x_1575_)) as u8;
                    if v_isSharedCheck_1647_ == 0 {
                        v___x_1578_ = v___x_1575_;
                        v_isShared_1579_ = v_isSharedCheck_1647_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1576_);
                        lean_dec(v___x_1575_);
                        v___x_1578_ = lean_box(0);
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
                lean_inc(v_a_1576_);
                v___x_1581_ = l_Lean_Syntax_isOfKind(v_a_1576_, v___x_1580_);
                if v___x_1581_ == 0 {
                    v_ref_1582_ = lean_ctor_get(v_a_1571_, 5);
                    v___x_1583_ = l_Lean_SourceInfo_fromRef(v_ref_1582_, v___x_1581_);
                    v___x_1584_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1585_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                    v___x_1586_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Syntax_node1(v___x_1583_, v___x_1586_, v_a_1576_);
                    v___x_1588_ =
                        l_Lean_Syntax_node2(v___x_1583_, v___x_1584_, v___x_1585_, v___x_1587_);
                    if v_isShared_1579_ == 0 {
                        lean_ctor_set(v___x_1578_, 0, v___x_1588_);
                        v___x_1590_ = v___x_1578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
                        v___x_1590_ = v_reuseFailAlloc_1591_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1592_ = lean_unsigned_to_nat(1);
                    v___x_1593_ = l_Lean_Syntax_getArg(v_a_1576_, v___x_1592_);
                    v___x_1594_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    lean_inc(v___x_1593_);
                    v___x_1595_ = l_Lean_Syntax_isOfKind(v___x_1593_, v___x_1594_);
                    if v___x_1595_ == 0 {
                        lean_dec(v___x_1593_);
                        v_ref_1596_ = lean_ctor_get(v_a_1571_, 5);
                        v___x_1597_ = l_Lean_SourceInfo_fromRef(v_ref_1596_, v___x_1595_);
                        v___x_1598_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1599_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                        v___x_1600_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        lean_inc(v___x_1597_);
                        v___x_1601_ = l_Lean_Syntax_node1(v___x_1597_, v___x_1600_, v_a_1576_);
                        v___x_1602_ =
                            l_Lean_Syntax_node2(v___x_1597_, v___x_1598_, v___x_1599_, v___x_1601_);
                        if v_isShared_1579_ == 0 {
                            lean_ctor_set(v___x_1578_, 0, v___x_1602_);
                            v___x_1604_ = v___x_1578_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                            v___x_1604_ = v_reuseFailAlloc_1605_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1606_ = lean_unsigned_to_nat(0);
                        v___x_1607_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1592_);
                        v___x_1608_ = l_Lean_Syntax_matchesNull(v___x_1607_, v___x_1606_);
                        if v___x_1608_ == 0 {
                            lean_dec(v___x_1593_);
                            v_ref_1609_ = lean_ctor_get(v_a_1571_, 5);
                            v___x_1610_ = l_Lean_SourceInfo_fromRef(v_ref_1609_, v___x_1608_);
                            v___x_1611_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1612_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__6);
                            v___x_1613_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            lean_inc(v___x_1610_);
                            v___x_1614_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1613_, v_a_1576_);
                            v___x_1615_ = l_Lean_Syntax_node2(
                                v___x_1610_,
                                v___x_1611_,
                                v___x_1612_,
                                v___x_1614_,
                            );
                            if v_isShared_1579_ == 0 {
                                lean_ctor_set(v___x_1578_, 0, v___x_1615_);
                                v___x_1617_ = v___x_1578_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
                                v___x_1617_ = v_reuseFailAlloc_1618_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1578_);
                            lean_dec(v_a_1576_);
                            v___x_1619_ = lean_unsigned_to_nat(3);
                            v___x_1620_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1619_);
                            v___x_1621_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1620_, v_a_1571_);
                            if lean_obj_tag(v___x_1621_) == 0 {
                                v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
                                v_isSharedCheck_1646_ = (!lean_is_exclusive(v___x_1621_)) as u8;
                                if v_isSharedCheck_1646_ == 0 {
                                    v___x_1624_ = v___x_1621_;
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_1622_);
                                    lean_dec(v___x_1621_);
                                    v___x_1624_ = lean_box(0);
                                    v_isShared_1625_ = v_isSharedCheck_1646_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1593_);
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
                v_ref_1626_ = lean_ctor_get(v_a_1571_, 5);
                v___x_1627_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1606_);
                lean_dec(v___x_1593_);
                v___x_1628_ = l_Lean_Syntax_getArgs(v___x_1627_);
                lean_dec(v___x_1627_);
                v___x_1629_ = 0;
                v___x_1630_ = l_Lean_SourceInfo_fromRef(v_ref_1626_, v___x_1629_);
                v___x_1631_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__8;
                v___x_1632_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1633_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                lean_inc_n(v___x_1630_, 4);
                v___x_1634_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1634_, 0, v___x_1630_);
                lean_ctor_set(v___x_1634_, 1, v___x_1632_);
                lean_ctor_set(v___x_1634_, 2, v___x_1633_);
                v___x_1635_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__11;
                v___x_1636_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1636_, 0, v___x_1630_);
                lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                v___x_1637_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1638_ = l_Array_append___redArg(v___x_1633_, v___x_1628_);
                lean_dec_ref(v___x_1628_);
                v___x_1639_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1639_, 0, v___x_1630_);
                lean_ctor_set(v___x_1639_, 1, v___x_1637_);
                lean_ctor_set(v___x_1639_, 2, v___x_1638_);
                v___x_1640_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1641_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1641_, 0, v___x_1630_);
                lean_ctor_set(v___x_1641_, 1, v___x_1640_);
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
                    lean_ctor_set(v___x_1624_, 0, v___x_1642_);
                    v___x_1644_ = v___x_1624_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
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
    mut v_a_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
    mut v_a_1652_: *mut LeanObject,
    mut v_a_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1655_: *mut LeanObject = core::ptr::null_mut();
    v_res_1655_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow(
        v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_,
    );
    lean_dec(v_a_1653_);
    lean_dec_ref(v_a_1652_);
    lean_dec(v_a_1651_);
    lean_dec_ref(v_a_1650_);
    lean_dec(v_a_1649_);
    lean_dec_ref(v_a_1648_);
    return v_res_1655_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___redArg(v___y_1656_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0___boxed(
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__0(v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
    lean_dec(v___y_1669_);
    lean_dec_ref(v___y_1668_);
    lean_dec(v___y_1667_);
    lean_dec_ref(v___y_1666_);
    lean_dec(v___y_1665_);
    lean_dec_ref(v___y_1664_);
    return v_res_1671_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(
    mut v_00_u03b1_1672_: *mut LeanObject,
    mut v_child_1673_: *mut LeanObject,
    mut v_childIdx_1674_: *mut LeanObject,
    mut v_x_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___redArg(v_child_1673_, v_childIdx_1674_, v_x_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1___boxed(
    mut v_00_u03b1_1684_: *mut LeanObject,
    mut v_child_1685_: *mut LeanObject,
    mut v_childIdx_1686_: *mut LeanObject,
    mut v_x_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1695_: *mut LeanObject = core::ptr::null_mut();
    v_res_1695_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at___00Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0_spec__1(v_00_u03b1_1684_, v_child_1685_, v_childIdx_1686_, v_x_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
    lean_dec(v___y_1693_);
    lean_dec_ref(v___y_1692_);
    lean_dec(v___y_1691_);
    lean_dec_ref(v___y_1690_);
    lean_dec(v___y_1689_);
    lean_dec_ref(v___y_1688_);
    return v_res_1695_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(
    mut v_00_u03b1_1696_: *mut LeanObject,
    mut v_x_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    v___x_1705_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v_x_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
    return v___x_1705_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___boxed(
    mut v_00_u03b1_1706_: *mut LeanObject,
    mut v_x_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
    mut v___y_1712_: *mut LeanObject,
    mut v___y_1713_: *mut LeanObject,
    mut v___y_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1715_: *mut LeanObject = core::ptr::null_mut();
    v_res_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0(v_00_u03b1_1706_, v_x_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
    lean_dec(v___y_1713_);
    lean_dec_ref(v___y_1712_);
    lean_dec(v___y_1711_);
    lean_dec_ref(v___y_1710_);
    lean_dec(v___y_1709_);
    lean_dec_ref(v___y_1708_);
    return v_res_1715_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(
    mut v_x_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v_x_1716_, v___y_1721_);
    return v___x_1724_;
}
pub unsafe fn l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___boxed(
    mut v_x_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1733_: *mut LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1(v_x_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    lean_dec(v___y_1731_);
    lean_dec_ref(v___y_1730_);
    lean_dec(v___y_1729_);
    lean_dec_ref(v___y_1728_);
    lean_dec(v___y_1727_);
    lean_dec_ref(v___y_1726_);
    return v_res_1733_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1()
-> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1773_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1774_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__0;
    v___x_1775_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1___closed__15;
    v___x_1776_ = lean_alloc_closure(
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
    mut v_a_1778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1779_: *mut LeanObject = core::ptr::null_mut();
    v_res_1779_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    return v_res_1779_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2()
-> *mut LeanObject {
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    v___x_1786_ =
        l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__1;
    v___x_1787_ = lean_mk_syntax_ident(v___x_1786_);
    return v___x_1787_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
    mut v_a_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
    mut v_a_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: u8 = 0;
    let mut v_ref_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v_ref_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: u8 = 0;
    let mut v_ref_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v_ref_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1801_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__0;
                v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__0___redArg(v___x_1801_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
                if lean_obj_tag(v___x_1802_) == 0 {
                    v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
                    v_isSharedCheck_1874_ = (!lean_is_exclusive(v___x_1802_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1805_ = v___x_1802_;
                        v_isShared_1806_ = v_isSharedCheck_1874_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1803_);
                        lean_dec(v___x_1802_);
                        v___x_1805_ = lean_box(0);
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
                lean_inc(v_a_1803_);
                v___x_1808_ = l_Lean_Syntax_isOfKind(v_a_1803_, v___x_1807_);
                if v___x_1808_ == 0 {
                    v_ref_1809_ = lean_ctor_get(v_a_1798_, 5);
                    v___x_1810_ = l_Lean_SourceInfo_fromRef(v_ref_1809_, v___x_1808_);
                    v___x_1811_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                    v___x_1812_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                    v___x_1813_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                    lean_inc(v___x_1810_);
                    v___x_1814_ = l_Lean_Syntax_node1(v___x_1810_, v___x_1813_, v_a_1803_);
                    v___x_1815_ =
                        l_Lean_Syntax_node2(v___x_1810_, v___x_1811_, v___x_1812_, v___x_1814_);
                    if v_isShared_1806_ == 0 {
                        lean_ctor_set(v___x_1805_, 0, v___x_1815_);
                        v___x_1817_ = v___x_1805_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
                        v___x_1817_ = v_reuseFailAlloc_1818_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1819_ = lean_unsigned_to_nat(1);
                    v___x_1820_ = l_Lean_Syntax_getArg(v_a_1803_, v___x_1819_);
                    v___x_1821_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__46;
                    lean_inc(v___x_1820_);
                    v___x_1822_ = l_Lean_Syntax_isOfKind(v___x_1820_, v___x_1821_);
                    if v___x_1822_ == 0 {
                        lean_dec(v___x_1820_);
                        v_ref_1823_ = lean_ctor_get(v_a_1798_, 5);
                        v___x_1824_ = l_Lean_SourceInfo_fromRef(v_ref_1823_, v___x_1822_);
                        v___x_1825_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                        v___x_1826_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                        v___x_1827_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                        lean_inc(v___x_1824_);
                        v___x_1828_ = l_Lean_Syntax_node1(v___x_1824_, v___x_1827_, v_a_1803_);
                        v___x_1829_ =
                            l_Lean_Syntax_node2(v___x_1824_, v___x_1825_, v___x_1826_, v___x_1828_);
                        if v_isShared_1806_ == 0 {
                            lean_ctor_set(v___x_1805_, 0, v___x_1829_);
                            v___x_1831_ = v___x_1805_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                            v___x_1831_ = v_reuseFailAlloc_1832_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1833_ = lean_unsigned_to_nat(0);
                        v___x_1834_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1819_);
                        v___x_1835_ = l_Lean_Syntax_matchesNull(v___x_1834_, v___x_1833_);
                        if v___x_1835_ == 0 {
                            lean_dec(v___x_1820_);
                            v_ref_1836_ = lean_ctor_get(v_a_1798_, 5);
                            v___x_1837_ = l_Lean_SourceInfo_fromRef(v_ref_1836_, v___x_1835_);
                            v___x_1838_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__2;
                            v___x_1839_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__2);
                            v___x_1840_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                            lean_inc(v___x_1837_);
                            v___x_1841_ = l_Lean_Syntax_node1(v___x_1837_, v___x_1840_, v_a_1803_);
                            v___x_1842_ = l_Lean_Syntax_node2(
                                v___x_1837_,
                                v___x_1838_,
                                v___x_1839_,
                                v___x_1841_,
                            );
                            if v_isShared_1806_ == 0 {
                                lean_ctor_set(v___x_1805_, 0, v___x_1842_);
                                v___x_1844_ = v___x_1805_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
                                v___x_1844_ = v_reuseFailAlloc_1845_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1805_);
                            lean_dec(v_a_1803_);
                            v___x_1846_ = lean_unsigned_to_nat(3);
                            v___x_1847_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1846_);
                            v___x_1848_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg(v___x_1847_, v_a_1798_);
                            if lean_obj_tag(v___x_1848_) == 0 {
                                v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
                                v_isSharedCheck_1873_ = (!lean_is_exclusive(v___x_1848_)) as u8;
                                if v_isSharedCheck_1873_ == 0 {
                                    v___x_1851_ = v___x_1848_;
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_1849_);
                                    lean_dec(v___x_1848_);
                                    v___x_1851_ = lean_box(0);
                                    v_isShared_1852_ = v_isSharedCheck_1873_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1820_);
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
                v_ref_1853_ = lean_ctor_get(v_a_1798_, 5);
                v___x_1854_ = l_Lean_Syntax_getArg(v___x_1820_, v___x_1833_);
                lean_dec(v___x_1820_);
                v___x_1855_ = l_Lean_Syntax_getArgs(v___x_1854_);
                lean_dec(v___x_1854_);
                v___x_1856_ = 0;
                v___x_1857_ = l_Lean_SourceInfo_fromRef(v_ref_1853_, v___x_1856_);
                v___x_1858_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__4;
                v___x_1859_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___closed__10;
                v___x_1860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47), core::ptr::addr_of_mut!(l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47_once), _init_l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__47);
                lean_inc_n(v___x_1857_, 4);
                v___x_1861_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1861_, 0, v___x_1857_);
                lean_ctor_set(v___x_1861_, 1, v___x_1859_);
                lean_ctor_set(v___x_1861_, 2, v___x_1860_);
                v___x_1862_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___closed__5;
                v___x_1863_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1863_, 0, v___x_1857_);
                lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                v___x_1864_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__43;
                v___x_1865_ = l_Array_append___redArg(v___x_1860_, v___x_1855_);
                lean_dec_ref(v___x_1855_);
                v___x_1866_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1866_, 0, v___x_1857_);
                lean_ctor_set(v___x_1866_, 1, v___x_1864_);
                lean_ctor_set(v___x_1866_, 2, v___x_1865_);
                v___x_1867_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__48;
                v___x_1868_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1868_, 0, v___x_1857_);
                lean_ctor_set(v___x_1868_, 1, v___x_1867_);
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
                    lean_ctor_set(v___x_1851_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1851_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
    mut v_a_1875_: *mut LeanObject,
    mut v_a_1876_: *mut LeanObject,
    mut v_a_1877_: *mut LeanObject,
    mut v_a_1878_: *mut LeanObject,
    mut v_a_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_res_1882_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow(
        v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_,
    );
    lean_dec(v_a_1880_);
    lean_dec_ref(v_a_1879_);
    lean_dec(v_a_1878_);
    lean_dec_ref(v_a_1877_);
    lean_dec(v_a_1876_);
    lean_dec_ref(v_a_1875_);
    return v_res_1882_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1()
-> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
    v___x_1892_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__0;
    v___x_1893_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1___closed__2;
    v___x_1894_ = lean_alloc_closure(
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
    mut v_a_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    return v_res_1897_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = lean_box(0);
    v___x_1899_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1900_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    lean_ctor_set(v___x_1900_, 1, v___x_1898_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    v___x_1902_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___closed__0);
    v___x_1903_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1903_, 0, v___x_1902_);
    return v___x_1903_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg___boxed(
    mut v___y_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v_res_1905_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(
    mut v_00_u03b1_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
    mut v___y_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
    return v___x_1914_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___boxed(
    mut v_00_u03b1_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0(v_00_u03b1_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_, v___y_1921_);
    lean_dec(v___y_1921_);
    lean_dec_ref(v___y_1920_);
    lean_dec(v___y_1919_);
    lean_dec_ref(v___y_1918_);
    lean_dec(v___y_1917_);
    lean_dec_ref(v___y_1916_);
    return v_res_1923_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(
    mut v_e_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_unused_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1927_ = l_Lean_Expr_hasMVar(v_e_1924_);
                if v___x_1927_ == 0 {
                    v___x_1928_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1928_, 0, v_e_1924_);
                    return v___x_1928_;
                } else {
                    v___x_1929_ = lean_st_ref_get(v___y_1925_);
                    v_mctx_1930_ = lean_ctor_get(v___x_1929_, 0);
                    lean_inc_ref(v_mctx_1930_);
                    lean_dec(v___x_1929_);
                    v___x_1931_ = l_Lean_instantiateMVarsCore(v_mctx_1930_, v_e_1924_);
                    v_fst_1932_ = lean_ctor_get(v___x_1931_, 0);
                    lean_inc(v_fst_1932_);
                    v_snd_1933_ = lean_ctor_get(v___x_1931_, 1);
                    lean_inc(v_snd_1933_);
                    lean_dec_ref(v___x_1931_);
                    v___x_1934_ = lean_st_ref_take(v___y_1925_);
                    v_cache_1935_ = lean_ctor_get(v___x_1934_, 1);
                    v_zetaDeltaFVarIds_1936_ = lean_ctor_get(v___x_1934_, 2);
                    v_postponed_1937_ = lean_ctor_get(v___x_1934_, 3);
                    v_diag_1938_ = lean_ctor_get(v___x_1934_, 4);
                    v_isSharedCheck_1947_ = (!lean_is_exclusive(v___x_1934_)) as u8;
                    if v_isSharedCheck_1947_ == 0 {
                        v_unused_1948_ = lean_ctor_get(v___x_1934_, 0);
                        lean_dec(v_unused_1948_);
                        v___x_1940_ = v___x_1934_;
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1938_);
                        lean_inc(v_postponed_1937_);
                        lean_inc(v_zetaDeltaFVarIds_1936_);
                        lean_inc(v_cache_1935_);
                        lean_dec(v___x_1934_);
                        v___x_1940_ = lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1947_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1941_ == 0 {
                    lean_ctor_set(v___x_1940_, 0, v_snd_1933_);
                    v___x_1943_ = v___x_1940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_snd_1933_);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_cache_1935_);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 2, v_zetaDeltaFVarIds_1936_);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 3, v_postponed_1937_);
                    lean_ctor_set(v_reuseFailAlloc_1946_, 4, v_diag_1938_);
                    v___x_1943_ = v_reuseFailAlloc_1946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1944_ = lean_st_ref_set(v___y_1925_, v___x_1943_);
                v___x_1945_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1945_, 0, v_fst_1932_);
                return v___x_1945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg___boxed(
    mut v_e_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1952_: *mut LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1949_, v___y_1950_);
    lean_dec(v___y_1950_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(
    mut v_e_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_e_1953_, v___y_1957_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___boxed(
    mut v_e_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1(v_e_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
    lean_dec(v___y_1968_);
    lean_dec_ref(v___y_1967_);
    lean_dec(v___y_1966_);
    lean_dec_ref(v___y_1965_);
    lean_dec(v___y_1964_);
    lean_dec_ref(v___y_1963_);
    return v_res_1970_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(
    mut v_msgData_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = lean_st_ref_get(v___y_1975_);
    v_env_1978_ = lean_ctor_get(v___x_1977_, 0);
    lean_inc_ref(v_env_1978_);
    lean_dec(v___x_1977_);
    v___x_1979_ = lean_st_ref_get(v___y_1973_);
    v_mctx_1980_ = lean_ctor_get(v___x_1979_, 0);
    lean_inc_ref(v_mctx_1980_);
    lean_dec(v___x_1979_);
    v_lctx_1981_ = lean_ctor_get(v___y_1972_, 2);
    v_options_1982_ = lean_ctor_get(v___y_1974_, 2);
    lean_inc_ref(v_options_1982_);
    lean_inc_ref(v_lctx_1981_);
    v___x_1983_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1983_, 0, v_env_1978_);
    lean_ctor_set(v___x_1983_, 1, v_mctx_1980_);
    lean_ctor_set(v___x_1983_, 2, v_lctx_1981_);
    lean_ctor_set(v___x_1983_, 3, v_options_1982_);
    v___x_1984_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1984_, 0, v___x_1983_);
    lean_ctor_set(v___x_1984_, 1, v_msgData_1971_);
    v___x_1985_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    return v___x_1985_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2___boxed(
    mut v_msgData_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1992_: *mut LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msgData_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
    lean_dec(v___y_1990_);
    lean_dec_ref(v___y_1989_);
    lean_dec(v___y_1988_);
    lean_dec_ref(v___y_1987_);
    return v_res_1992_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    v___x_1993_ = lean_box(1);
    v___x_1994_ = l_Lean_MessageData_ofFormat(v___x_1993_);
    return v___x_1994_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    v___x_1998_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__2;
    v___x_1999_ = l_Lean_MessageData_ofFormat(v___x_1998_);
    return v___x_1999_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(
    mut v_x_2000_: *mut LeanObject,
    mut v_x_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v_before_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2010_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_unused_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2001_) == 0 {
                    return v_x_2000_;
                } else {
                    v_head_2002_ = lean_ctor_get(v_x_2001_, 0);
                    v_tail_2003_ = lean_ctor_get(v_x_2001_, 1);
                    v_isSharedCheck_2025_ = (!lean_is_exclusive(v_x_2001_)) as u8;
                    if v_isSharedCheck_2025_ == 0 {
                        v___x_2005_ = v_x_2001_;
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2003_);
                        lean_inc(v_head_2002_);
                        lean_dec(v_x_2001_);
                        v___x_2005_ = lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2007_ = lean_ctor_get(v_head_2002_, 0);
                v_isSharedCheck_2023_ = (!lean_is_exclusive(v_head_2002_)) as u8;
                if v_isSharedCheck_2023_ == 0 {
                    v_unused_2024_ = lean_ctor_get(v_head_2002_, 1);
                    lean_dec(v_unused_2024_);
                    v___x_2009_ = v_head_2002_;
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_2007_);
                    lean_dec(v_head_2002_);
                    v___x_2009_ = lean_box(0);
                    v_isShared_2010_ = v_isSharedCheck_2023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2011_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2010_ == 0 {
                    lean_ctor_set_tag(v___x_2009_, 7);
                    lean_ctor_set(v___x_2009_, 1, v___x_2011_);
                    lean_ctor_set(v___x_2009_, 0, v_x_2000_);
                    v___x_2013_ = v___x_2009_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_x_2000_);
                    lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_2011_);
                    v___x_2013_ = v_reuseFailAlloc_2022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2014_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__3);
                if v_isShared_2006_ == 0 {
                    lean_ctor_set_tag(v___x_2005_, 7);
                    lean_ctor_set(v___x_2005_, 1, v___x_2014_);
                    lean_ctor_set(v___x_2005_, 0, v___x_2013_);
                    v___x_2016_ = v___x_2005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2021_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___x_2014_);
                    v___x_2016_ = v_reuseFailAlloc_2021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2017_ = l_Lean_MessageData_ofSyntax(v_before_2007_);
                v___x_2018_ = l_Lean_indentD(v___x_2017_);
                v___x_2019_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2019_, 0, v___x_2016_);
                lean_ctor_set(v___x_2019_, 1, v___x_2018_);
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
    mut v_opts_2026_: *mut LeanObject,
    mut v_opt_2027_: *mut LeanObject,
) -> u8 {
    let mut v_name_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v_name_2028_ = lean_ctor_get(v_opt_2027_, 0);
    v_defValue_2029_ = lean_ctor_get(v_opt_2027_, 1);
    v_map_2030_ = lean_ctor_get(v_opts_2026_, 0);
    v___x_2031_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2030_,
            v_name_2028_,
        );
    if lean_obj_tag(v___x_2031_) == 0 {
        let mut v___x_2032_: u8 = 0;
        v___x_2032_ = (lean_unbox(v_defValue_2029_) as u8);
        return v___x_2032_;
    } else {
        let mut v_val_2033_: *mut LeanObject = core::ptr::null_mut();
        v_val_2033_ = lean_ctor_get(v___x_2031_, 0);
        lean_inc(v_val_2033_);
        lean_dec_ref_known(v___x_2031_, 1);
        if lean_obj_tag(v_val_2033_) == 1 {
            let mut v_v_2034_: u8 = 0;
            v_v_2034_ = lean_ctor_get_uint8(v_val_2033_, 0 as u32);
            lean_dec_ref_known(v_val_2033_, 0);
            return v_v_2034_;
        } else {
            let mut v___x_2035_: u8 = 0;
            lean_dec(v_val_2033_);
            v___x_2035_ = (lean_unbox(v_defValue_2029_) as u8);
            return v___x_2035_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4___boxed(
    mut v_opts_2036_: *mut LeanObject,
    mut v_opt_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2038_: u8 = 0;
    let mut v_r_2039_: *mut LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_opts_2036_, v_opt_2037_);
    lean_dec_ref(v_opt_2037_);
    lean_dec_ref(v_opts_2036_);
    v_r_2039_ = lean_box((v_res_2038_) as usize);
    return v_r_2039_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2043_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__1;
    v___x_2044_ = l_Lean_MessageData_ofFormat(v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(
    mut v_msgData_2045_: *mut LeanObject,
    mut v_macroStack_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_unused_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2049_ = lean_ctor_get(v___y_2047_, 2);
                v___x_2050_ = l_Lean_Elab_pp_macroStack;
                v___x_2051_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__4(v_options_2049_, v___x_2050_);
                if v___x_2051_ == 0 {
                    lean_dec(v_macroStack_2046_);
                    v___x_2052_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2052_, 0, v_msgData_2045_);
                    return v___x_2052_;
                } else {
                    if lean_obj_tag(v_macroStack_2046_) == 0 {
                        v___x_2053_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2053_, 0, v_msgData_2045_);
                        return v___x_2053_;
                    } else {
                        v_head_2054_ = lean_ctor_get(v_macroStack_2046_, 0);
                        lean_inc(v_head_2054_);
                        v_after_2055_ = lean_ctor_get(v_head_2054_, 1);
                        v_isSharedCheck_2070_ = (!lean_is_exclusive(v_head_2054_)) as u8;
                        if v_isSharedCheck_2070_ == 0 {
                            v_unused_2071_ = lean_ctor_get(v_head_2054_, 0);
                            lean_dec(v_unused_2071_);
                            v___x_2057_ = v_head_2054_;
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_2055_);
                            lean_dec(v_head_2054_);
                            v___x_2057_ = lean_box(0);
                            v_isShared_2058_ = v_isSharedCheck_2070_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2059_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5___closed__0);
                if v_isShared_2058_ == 0 {
                    lean_ctor_set_tag(v___x_2057_, 7);
                    lean_ctor_set(v___x_2057_, 1, v___x_2059_);
                    lean_ctor_set(v___x_2057_, 0, v_msgData_2045_);
                    v___x_2061_ = v___x_2057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_msgData_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2059_);
                    v___x_2061_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2062_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___closed__2);
                v___x_2063_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                v___x_2064_ = l_Lean_MessageData_ofSyntax(v_after_2055_);
                v___x_2065_ = l_Lean_indentD(v___x_2064_);
                v_msgData_2066_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_2066_, 0, v___x_2063_);
                lean_ctor_set(v_msgData_2066_, 1, v___x_2065_);
                v___x_2067_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3_spec__5(v_msgData_2066_, v_macroStack_2046_);
                v___x_2068_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2068_, 0, v___x_2067_);
                return v___x_2068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg___boxed(
    mut v_msgData_2072_: *mut LeanObject,
    mut v_macroStack_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2076_: *mut LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2072_, v_macroStack_2073_, v___y_2074_);
    lean_dec_ref(v___y_2074_);
    return v_res_2076_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(
    mut v_msg_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2085_ = lean_ctor_get(v___y_2082_, 5);
                v___x_2086_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__2(v_msg_2077_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
                v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
                lean_inc(v_a_2087_);
                lean_dec_ref(v___x_2086_);
                v_macroStack_2088_ = lean_ctor_get(v___y_2078_, 1);
                v___x_2089_ = l_Lean_Elab_getBetterRef(v_ref_2085_, v_macroStack_2088_);
                lean_inc(v_macroStack_2088_);
                v___x_2090_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_a_2087_, v_macroStack_2088_, v___y_2082_);
                v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
                v_isSharedCheck_2099_ = (!lean_is_exclusive(v___x_2090_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2093_ = v___x_2090_;
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2091_);
                    lean_dec(v___x_2090_);
                    v___x_2093_ = lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2095_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2095_, 0, v___x_2089_);
                lean_ctor_set(v___x_2095_, 1, v_a_2091_);
                if v_isShared_2094_ == 0 {
                    lean_ctor_set_tag(v___x_2093_, 1);
                    lean_ctor_set(v___x_2093_, 0, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
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
    mut v_msg_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2108_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
    lean_dec(v___y_2106_);
    lean_dec_ref(v___y_2105_);
    lean_dec(v___y_2104_);
    lean_dec_ref(v___y_2103_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    return v_res_2108_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__12;
    v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
    return v___x_2141_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__14;
    v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__16;
    v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
    return v___x_2147_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
    mut v_x_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2171_: u8 = 0;
    let mut v_cancelTk_x3f_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2173_: u8 = 0;
    let mut v_inheritedTraceOptions_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2249_: u8 = 0;
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2319_: u8 = 0;
    let mut v_a_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2156_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
                lean_inc(v_x_2148_);
                v___x_2157_ = l_Lean_Syntax_isOfKind(v_x_2148_, v___x_2156_);
                if v___x_2157_ == 0 {
                    lean_dec(v_x_2148_);
                    v___x_2158_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__0___redArg();
                    return v___x_2158_;
                } else {
                    v_fileName_2159_ = lean_ctor_get(v_a_2153_, 0);
                    v_fileMap_2160_ = lean_ctor_get(v_a_2153_, 1);
                    v_options_2161_ = lean_ctor_get(v_a_2153_, 2);
                    v_currRecDepth_2162_ = lean_ctor_get(v_a_2153_, 3);
                    v_maxRecDepth_2163_ = lean_ctor_get(v_a_2153_, 4);
                    v_ref_2164_ = lean_ctor_get(v_a_2153_, 5);
                    v_currNamespace_2165_ = lean_ctor_get(v_a_2153_, 6);
                    v_openDecls_2166_ = lean_ctor_get(v_a_2153_, 7);
                    v_initHeartbeats_2167_ = lean_ctor_get(v_a_2153_, 8);
                    v_maxHeartbeats_2168_ = lean_ctor_get(v_a_2153_, 9);
                    v_quotContext_2169_ = lean_ctor_get(v_a_2153_, 10);
                    v_currMacroScope_2170_ = lean_ctor_get(v_a_2153_, 11);
                    v_diag_2171_ = lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_2172_ = lean_ctor_get(v_a_2153_, 12);
                    v_suppressElabErrors_2173_ = lean_ctor_get_uint8(
                        v_a_2153_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_2174_ = lean_ctor_get(v_a_2153_, 13);
                    v___x_2175_ = lean_unsigned_to_nat(3);
                    v___x_2176_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2175_);
                    v___x_2177_ = lean_box(0);
                    v_ref_2178_ = l_Lean_replaceRef(v___x_2176_, v_ref_2164_);
                    lean_inc_ref(v_inheritedTraceOptions_2174_);
                    lean_inc(v_cancelTk_x3f_2172_);
                    lean_inc(v_currMacroScope_2170_);
                    lean_inc(v_quotContext_2169_);
                    lean_inc(v_maxHeartbeats_2168_);
                    lean_inc(v_initHeartbeats_2167_);
                    lean_inc(v_openDecls_2166_);
                    lean_inc(v_currNamespace_2165_);
                    lean_inc(v_maxRecDepth_2163_);
                    lean_inc(v_currRecDepth_2162_);
                    lean_inc_ref(v_options_2161_);
                    lean_inc_ref(v_fileMap_2160_);
                    lean_inc_ref(v_fileName_2159_);
                    v___x_2179_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_2179_, 0, v_fileName_2159_);
                    lean_ctor_set(v___x_2179_, 1, v_fileMap_2160_);
                    lean_ctor_set(v___x_2179_, 2, v_options_2161_);
                    lean_ctor_set(v___x_2179_, 3, v_currRecDepth_2162_);
                    lean_ctor_set(v___x_2179_, 4, v_maxRecDepth_2163_);
                    lean_ctor_set(v___x_2179_, 5, v_ref_2178_);
                    lean_ctor_set(v___x_2179_, 6, v_currNamespace_2165_);
                    lean_ctor_set(v___x_2179_, 7, v_openDecls_2166_);
                    lean_ctor_set(v___x_2179_, 8, v_initHeartbeats_2167_);
                    lean_ctor_set(v___x_2179_, 9, v_maxHeartbeats_2168_);
                    lean_ctor_set(v___x_2179_, 10, v_quotContext_2169_);
                    lean_ctor_set(v___x_2179_, 11, v_currMacroScope_2170_);
                    lean_ctor_set(v___x_2179_, 12, v_cancelTk_x3f_2172_);
                    lean_ctor_set(v___x_2179_, 13, v_inheritedTraceOptions_2174_);
                    lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_2171_,
                    );
                    lean_ctor_set_uint8(
                        v___x_2179_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
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
                    if lean_obj_tag(v___x_2180_) == 0 {
                        v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
                        lean_inc_n(v_a_2181_, 2);
                        lean_dec_ref_known(v___x_2180_, 1);
                        lean_inc(v_a_2154_);
                        lean_inc_ref(v___x_2179_);
                        lean_inc(v_a_2152_);
                        lean_inc_ref(v_a_2151_);
                        v___x_2182_ = lean_infer_type(
                            v_a_2181_,
                            v_a_2151_,
                            v_a_2152_,
                            v___x_2179_,
                            v_a_2154_,
                        );
                        if lean_obj_tag(v___x_2182_) == 0 {
                            v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
                            lean_inc_n(v_a_2183_, 2);
                            lean_dec_ref_known(v___x_2182_, 1);
                            v___x_2184_ = l_Lean_Elab_Term_tryPostponeIfMVar(
                                v_a_2183_,
                                v_a_2149_,
                                v_a_2150_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if lean_obj_tag(v___x_2184_) == 0 {
                                lean_dec_ref_known(v___x_2184_, 1);
                                v___x_2185_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__1___redArg(v_a_2183_, v_a_2152_);
                                v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
                                v_isSharedCheck_2319_ = (!lean_is_exclusive(v___x_2185_)) as u8;
                                if v_isSharedCheck_2319_ == 0 {
                                    v___x_2188_ = v___x_2185_;
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2186_);
                                    lean_dec(v___x_2185_);
                                    v___x_2188_ = lean_box(0);
                                    v_isShared_2189_ = v_isSharedCheck_2319_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2183_);
                                lean_dec(v_a_2181_);
                                lean_dec_ref_known(v___x_2179_, 14);
                                lean_dec(v_x_2148_);
                                v_a_2320_ = lean_ctor_get(v___x_2184_, 0);
                                v_isSharedCheck_2327_ = (!lean_is_exclusive(v___x_2184_)) as u8;
                                if v_isSharedCheck_2327_ == 0 {
                                    v___x_2322_ = v___x_2184_;
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_2320_);
                                    lean_dec(v___x_2184_);
                                    v___x_2322_ = lean_box(0);
                                    v_isShared_2323_ = v_isSharedCheck_2327_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2181_);
                            lean_dec_ref_known(v___x_2179_, 14);
                            lean_dec(v_x_2148_);
                            return v___x_2182_;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2179_, 14);
                        lean_dec(v_x_2148_);
                        return v___x_2180_;
                    }
                }
            }
            1 => {
                v___x_2190_ = lean_unsigned_to_nat(1);
                v___x_2191_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2190_);
                v___x_2192_ = lean_unsigned_to_nat(5);
                v___x_2193_ = l_Lean_Syntax_getArg(v_x_2148_, v___x_2192_);
                lean_dec(v_x_2148_);
                v___x_2254_ = l_Lean_Expr_consumeMData(v_a_2186_);
                if lean_obj_tag(v___x_2254_) == 5 {
                    v_fn_2255_ = lean_ctor_get(v___x_2254_, 0);
                    lean_inc_ref(v_fn_2255_);
                    v_arg_2256_ = lean_ctor_get(v___x_2254_, 1);
                    lean_inc_ref_n(v_arg_2256_, 2);
                    lean_dec_ref_known(v___x_2254_, 2);
                    v___x_2257_ = l_Lean_Meta_getLevel(
                        v_arg_2256_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    if lean_obj_tag(v___x_2257_) == 0 {
                        v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
                        lean_inc(v_a_2258_);
                        lean_dec_ref_known(v___x_2257_, 1);
                        v___x_2259_ = l_Lean_Level_dec(v_a_2258_);
                        lean_dec(v_a_2258_);
                        if lean_obj_tag(v___x_2259_) == 1 {
                            v_val_2260_ = lean_ctor_get(v___x_2259_, 0);
                            lean_inc(v_val_2260_);
                            lean_dec_ref_known(v___x_2259_, 1);
                            lean_inc(v_a_2186_);
                            v___x_2261_ = l_Lean_Meta_getLevel(
                                v_a_2186_,
                                v_a_2151_,
                                v_a_2152_,
                                v___x_2179_,
                                v_a_2154_,
                            );
                            if lean_obj_tag(v___x_2261_) == 0 {
                                v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
                                lean_inc(v_a_2262_);
                                lean_dec_ref_known(v___x_2261_, 1);
                                v___x_2263_ = l_Lean_Level_dec(v_a_2262_);
                                lean_dec(v_a_2262_);
                                if lean_obj_tag(v___x_2263_) == 1 {
                                    lean_dec(v_a_2186_);
                                    v_val_2264_ = lean_ctor_get(v___x_2263_, 0);
                                    v_isSharedCheck_2286_ = (!lean_is_exclusive(v___x_2263_)) as u8;
                                    if v_isSharedCheck_2286_ == 0 {
                                        v___x_2266_ = v___x_2263_;
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2264_);
                                        lean_dec(v___x_2263_);
                                        v___x_2266_ = lean_box(0);
                                        v_isShared_2267_ = v_isSharedCheck_2286_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_2263_);
                                    lean_dec(v_val_2260_);
                                    lean_dec_ref(v_arg_2256_);
                                    lean_dec_ref(v_fn_2255_);
                                    lean_dec(v___x_2193_);
                                    lean_dec(v___x_2191_);
                                    lean_del_object(v___x_2188_);
                                    lean_dec(v_a_2181_);
                                    v___x_2287_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                                    v___x_2288_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                                    v___x_2289_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_2289_, 0, v___x_2287_);
                                    lean_ctor_set(v___x_2289_, 1, v___x_2288_);
                                    v___x_2290_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2289_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                                    lean_dec_ref_known(v___x_2179_, 14);
                                    v___y_2245_ = v___x_2290_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                lean_dec(v_val_2260_);
                                lean_dec_ref(v_arg_2256_);
                                lean_dec_ref(v_fn_2255_);
                                lean_dec(v___x_2193_);
                                lean_dec(v___x_2191_);
                                lean_del_object(v___x_2188_);
                                lean_dec(v_a_2186_);
                                lean_dec(v_a_2181_);
                                lean_dec_ref_known(v___x_2179_, 14);
                                v_a_2291_ = lean_ctor_get(v___x_2261_, 0);
                                v_isSharedCheck_2298_ = (!lean_is_exclusive(v___x_2261_)) as u8;
                                if v_isSharedCheck_2298_ == 0 {
                                    v___x_2293_ = v___x_2261_;
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_2291_);
                                    lean_dec(v___x_2261_);
                                    v___x_2293_ = lean_box(0);
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2259_);
                            lean_dec_ref(v_arg_2256_);
                            lean_dec_ref(v_fn_2255_);
                            lean_dec(v___x_2193_);
                            lean_dec(v___x_2191_);
                            lean_del_object(v___x_2188_);
                            lean_dec(v_a_2181_);
                            v___x_2299_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__13);
                            v___x_2300_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                            v___x_2301_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_2301_, 0, v___x_2299_);
                            lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                            v___x_2302_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2301_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                            lean_dec_ref_known(v___x_2179_, 14);
                            v___y_2245_ = v___x_2302_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_2256_);
                        lean_dec_ref(v_fn_2255_);
                        lean_dec(v___x_2193_);
                        lean_dec(v___x_2191_);
                        lean_del_object(v___x_2188_);
                        lean_dec(v_a_2186_);
                        lean_dec(v_a_2181_);
                        lean_dec_ref_known(v___x_2179_, 14);
                        v_a_2303_ = lean_ctor_get(v___x_2257_, 0);
                        v_isSharedCheck_2310_ = (!lean_is_exclusive(v___x_2257_)) as u8;
                        if v_isSharedCheck_2310_ == 0 {
                            v___x_2305_ = v___x_2257_;
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_2303_);
                            lean_dec(v___x_2257_);
                            v___x_2305_ = lean_box(0);
                            v_isShared_2306_ = v_isSharedCheck_2310_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2254_);
                    lean_dec(v___x_2193_);
                    lean_dec(v___x_2191_);
                    lean_del_object(v___x_2188_);
                    v___x_2311_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__15);
                    v___x_2312_ = l_Lean_MessageData_ofExpr(v_a_2181_);
                    v___x_2313_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2313_, 0, v___x_2311_);
                    lean_ctor_set(v___x_2313_, 1, v___x_2312_);
                    v___x_2314_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17_once), _init_l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__17);
                    v___x_2315_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2315_, 0, v___x_2313_);
                    lean_ctor_set(v___x_2315_, 1, v___x_2314_);
                    v___x_2316_ = l_Lean_MessageData_ofExpr(v_a_2186_);
                    v___x_2317_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2317_, 0, v___x_2315_);
                    lean_ctor_set(v___x_2317_, 1, v___x_2316_);
                    v___x_2318_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v___x_2317_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v___x_2179_, v_a_2154_);
                    lean_dec_ref_known(v___x_2179_, 14);
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
                lean_inc_n(v___x_2203_, 2);
                v___x_2206_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2206_, 0, v___x_2203_);
                lean_ctor_set(v___x_2206_, 1, v___x_2205_);
                v___x_2207_ = l_Std_Do_SPred_Notation_unpack___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow_spec__1___redArg___closed__44;
                v___x_2208_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2208_, 0, v___x_2203_);
                lean_ctor_set(v___x_2208_, 1, v___x_2207_);
                v___x_2209_ = l_Lean_Syntax_node3(
                    v___x_2203_,
                    v___x_2204_,
                    v___x_2206_,
                    v___x_2191_,
                    v___x_2208_,
                );
                v___x_2210_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__4;
                v___x_2211_ = lean_box(0);
                lean_inc(v_fst_2195_);
                v___x_2212_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2212_, 0, v_fst_2195_);
                lean_ctor_set(v___x_2212_, 1, v___x_2211_);
                lean_inc_ref(v___x_2212_);
                v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
                lean_inc_ref(v_fst_2199_);
                v___x_2214_ = l_Lean_Expr_app___override(v___x_2213_, v_fst_2199_);
                if v_isShared_2189_ == 0 {
                    lean_ctor_set_tag(v___x_2188_, 1);
                    lean_ctor_set(v___x_2188_, 0, v___x_2214_);
                    v___x_2216_ = v___x_2188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2214_);
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
                if lean_obj_tag(v___x_2217_) == 0 {
                    v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
                    v_isSharedCheck_2242_ = (!lean_is_exclusive(v___x_2217_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2220_ = v___x_2217_;
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2218_);
                        lean_dec(v___x_2217_);
                        v___x_2220_ = lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2242_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_2212_, 2);
                    lean_dec_ref(v_snd_2201_);
                    lean_dec_ref(v_fst_2200_);
                    lean_dec_ref(v_fst_2199_);
                    lean_dec_ref(v_fst_2198_);
                    lean_dec_ref(v_fst_2197_);
                    lean_dec(v_fst_2196_);
                    lean_dec(v_fst_2195_);
                    lean_dec(v___x_2193_);
                    return v___x_2217_;
                }
            }
            4 => {
                v___x_2222_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__5;
                v___x_2223_ = l_Lean_mkConst(v___x_2222_, v___x_2212_);
                lean_inc_ref(v_fst_2199_);
                lean_inc_ref(v_fst_2198_);
                v___x_2224_ = l_Lean_mkAppB(v___x_2223_, v_fst_2198_, v_fst_2199_);
                if v_isShared_2221_ == 0 {
                    lean_ctor_set_tag(v___x_2220_, 1);
                    lean_ctor_set(v___x_2220_, 0, v___x_2224_);
                    v___x_2226_ = v___x_2220_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2224_);
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
                if lean_obj_tag(v___x_2227_) == 0 {
                    v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
                    v_isSharedCheck_2240_ = (!lean_is_exclusive(v___x_2227_)) as u8;
                    if v_isSharedCheck_2240_ == 0 {
                        v___x_2230_ = v___x_2227_;
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2228_);
                        lean_dec(v___x_2227_);
                        v___x_2230_ = lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2240_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2218_);
                    lean_dec_ref(v_snd_2201_);
                    lean_dec_ref(v_fst_2200_);
                    lean_dec_ref(v_fst_2199_);
                    lean_dec_ref(v_fst_2198_);
                    lean_dec_ref(v_fst_2197_);
                    lean_dec(v_fst_2196_);
                    lean_dec(v_fst_2195_);
                    return v___x_2227_;
                }
            }
            6 => {
                v___x_2232_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__7;
                v___x_2233_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2233_, 0, v_fst_2196_);
                lean_ctor_set(v___x_2233_, 1, v___x_2211_);
                v___x_2234_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2234_, 0, v_fst_2195_);
                lean_ctor_set(v___x_2234_, 1, v___x_2233_);
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
                    lean_ctor_set(v___x_2230_, 0, v___x_2236_);
                    v___x_2238_ = v___x_2230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2239_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2238_;
            }
            8 => {
                v_a_2246_ = lean_ctor_get(v___y_2245_, 0);
                v_isSharedCheck_2253_ = (!lean_is_exclusive(v___y_2245_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v___x_2248_ = v___y_2245_;
                    v_isShared_2249_ = v_isSharedCheck_2253_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_2246_);
                    lean_dec(v___y_2245_);
                    v___x_2248_ = lean_box(0);
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
                    v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
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
                v___x_2269_ = lean_box(0);
                lean_inc(v_val_2260_);
                v___x_2270_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2270_, 0, v_val_2260_);
                lean_ctor_set(v___x_2270_, 1, v___x_2269_);
                v___x_2271_ = l_Lean_mkConst(v___x_2268_, v___x_2270_);
                if v_isShared_2267_ == 0 {
                    lean_ctor_set(v___x_2266_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2266_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2285_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2274_ = 0;
                v___x_2275_ = lean_box(0);
                v___x_2276_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_2273_,
                    v___x_2274_,
                    v___x_2275_,
                    v_a_2151_,
                    v_a_2152_,
                    v___x_2179_,
                    v_a_2154_,
                );
                if lean_obj_tag(v___x_2276_) == 0 {
                    v_a_2277_ = lean_ctor_get(v___x_2276_, 0);
                    lean_inc_n(v_a_2277_, 2);
                    lean_dec_ref_known(v___x_2276_, 1);
                    v___x_2278_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__11;
                    lean_inc(v_val_2264_);
                    v___x_2279_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2279_, 0, v_val_2264_);
                    lean_ctor_set(v___x_2279_, 1, v___x_2269_);
                    lean_inc(v_val_2260_);
                    v___x_2280_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2280_, 0, v_val_2260_);
                    lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                    v___x_2281_ = l_Lean_mkConst(v___x_2278_, v___x_2280_);
                    lean_inc_ref(v_fn_2255_);
                    v___x_2282_ = l_Lean_mkAppB(v___x_2281_, v_fn_2255_, v_a_2277_);
                    v___x_2283_ = l_Lean_Meta_synthInstance(
                        v___x_2282_,
                        v___x_2177_,
                        v_a_2151_,
                        v_a_2152_,
                        v___x_2179_,
                        v_a_2154_,
                    );
                    lean_dec_ref_known(v___x_2179_, 14);
                    if lean_obj_tag(v___x_2283_) == 0 {
                        v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
                        lean_inc(v_a_2284_);
                        lean_dec_ref_known(v___x_2283_, 1);
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
                        lean_dec(v_a_2277_);
                        lean_dec(v_val_2264_);
                        lean_dec(v_val_2260_);
                        lean_dec_ref(v_arg_2256_);
                        lean_dec_ref(v_fn_2255_);
                        lean_dec(v___x_2193_);
                        lean_dec(v___x_2191_);
                        lean_del_object(v___x_2188_);
                        lean_dec(v_a_2181_);
                        return v___x_2283_;
                    }
                } else {
                    lean_dec(v_val_2264_);
                    lean_dec(v_val_2260_);
                    lean_dec_ref(v_arg_2256_);
                    lean_dec_ref(v_fn_2255_);
                    lean_dec(v___x_2193_);
                    lean_dec(v___x_2191_);
                    lean_del_object(v___x_2188_);
                    lean_dec(v_a_2181_);
                    lean_dec_ref_known(v___x_2179_, 14);
                    return v___x_2276_;
                }
            }
            13 => {
                if v_isShared_2294_ == 0 {
                    v___x_2296_ = v___x_2293_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
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
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
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
                    v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
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
    mut v_x_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
    mut v_a_2330_: *mut LeanObject,
    mut v_a_2331_: *mut LeanObject,
    mut v_a_2332_: *mut LeanObject,
    mut v_a_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2336_: *mut LeanObject = core::ptr::null_mut();
    v_res_2336_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_,
    );
    lean_dec(v_a_2334_);
    lean_dec_ref(v_a_2333_);
    lean_dec(v_a_2332_);
    lean_dec_ref(v_a_2331_);
    lean_dec(v_a_2330_);
    lean_dec_ref(v_a_2329_);
    return v_res_2336_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
    mut v_x_2337_: *mut LeanObject,
    mut v_x_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
    mut v_a_2341_: *mut LeanObject,
    mut v_a_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    v___x_2346_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg(
        v_x_2337_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_,
    );
    return v___x_2346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___boxed(
    mut v_x_2347_: *mut LeanObject,
    mut v_x_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
    mut v_a_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2356_: *mut LeanObject = core::ptr::null_mut();
    v_res_2356_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple(
        v_x_2347_, v_x_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_,
    );
    lean_dec(v_a_2354_);
    lean_dec_ref(v_a_2353_);
    lean_dec(v_a_2352_);
    lean_dec_ref(v_a_2351_);
    lean_dec(v_a_2350_);
    lean_dec_ref(v_a_2349_);
    lean_dec(v_x_2348_);
    return v_res_2356_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(
    mut v_00_u03b1_2357_: *mut LeanObject,
    mut v_msg_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
    mut v___y_2361_: *mut LeanObject,
    mut v___y_2362_: *mut LeanObject,
    mut v___y_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    v___x_2366_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___redArg(v_msg_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
    return v___x_2366_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2___boxed(
    mut v_00_u03b1_2367_: *mut LeanObject,
    mut v_msg_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
    mut v___y_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2376_: *mut LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2(v_00_u03b1_2367_, v_msg_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
    lean_dec(v___y_2374_);
    lean_dec_ref(v___y_2373_);
    lean_dec(v___y_2372_);
    lean_dec_ref(v___y_2371_);
    lean_dec(v___y_2370_);
    lean_dec_ref(v___y_2369_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(
    mut v_msgData_2377_: *mut LeanObject,
    mut v_macroStack_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___redArg(v_msgData_2377_, v_macroStack_2378_, v___y_2383_);
    return v___x_2386_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3___boxed(
    mut v_msgData_2387_: *mut LeanObject,
    mut v_macroStack_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
    mut v___y_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2396_: *mut LeanObject = core::ptr::null_mut();
    v_res_2396_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple_spec__2_spec__3(v_msgData_2387_, v_macroStack_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
    lean_dec(v___y_2394_);
    lean_dec_ref(v___y_2393_);
    lean_dec(v___y_2392_);
    lean_dec_ref(v___y_2391_);
    lean_dec(v___y_2390_);
    lean_dec_ref(v___y_2389_);
    return v_res_2396_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1()
-> *mut LeanObject {
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    v___x_2402_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_2403_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___redArg___closed__1;
    v___x_2404_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1___closed__1;
    v___x_2405_ = lean_alloc_closure(
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
    mut v_a_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2408_: *mut LeanObject = core::ptr::null_mut();
    v_res_2408_ = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    return v_res_2408_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondNoThrow__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_unexpandPostCondMayThrow__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple___regBuiltin___private_Lean_Elab_Tactic_Do_Syntax_0__Std_Do_elabTriple__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Syntax(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Do_Triple_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Syntax(builtin);
}
