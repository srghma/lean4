// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Have
// Imports: Lean.Elab.Tactic.Grind.Basic Lean.Meta.Tactic.Grind.Intro Lean.Meta.Tactic.Grind.RevertAll Lean.Elab.SyntheticMVars Lean.Meta.Tactic.Grind.Solve
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::l_Lean_Syntax_formatStx;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getId};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node5, l_Lean_addMacroScope, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::{
    initialize_Lean_Elab_SyntheticMVars, l_Lean_Elab_Term_PostponeBehavior_ofBool,
    l_Lean_Elab_Term_synthesizeSyntheticMVars, runtime_initialize_Lean_Elab_SyntheticMVars,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, l_Lean_Elab_Tactic_Grind_getGoals___redArg,
    l_Lean_Elab_Tactic_Grind_getMainGoal___redArg, l_Lean_Elab_Tactic_Grind_grindTacElabAttribute,
    l_Lean_Elab_Tactic_Grind_liftAction___redArg, l_Lean_Elab_Tactic_Grind_liftGrindM___redArg,
    l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg, l_Lean_Elab_Tactic_Grind_setGoals___redArg,
    l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg,
    l_Lean_Elab_Tactic_Grind_withMainContext___boxed,
    l_Lean_Elab_Tactic_Grind_withMainContext___redArg,
    runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_mkFreshExprMVar;
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::Grind::Intro::{
    initialize_Lean_Meta_Tactic_Grind_Intro, l_Lean_Meta_Grind_Action_intros___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    l_Lean_Meta_Grind_Result_toMessageData, l_Lean_Meta_Grind_mkResult___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::RevertAll::{
    initialize_Lean_Meta_Tactic_Grind_RevertAll, l_Lean_Meta_Grind_markGrindName,
    runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Solve::{
    initialize_Lean_Meta_Tactic_Grind_Solve, l_Lean_Meta_Grind_solve___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Solve,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_dbg_trace;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [114, 101, 117, 115, 101, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,129656885399133742 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject,8944050731725230368 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [114, 101, 117, 115, 101, 32, 115, 116, 111, 112, 112, 101, 100, 58, 32, 103, 117, 97, 114, 100, 32, 102, 97, 105, 108, 101, 100, 32, 97, 116, 32, 0]};
static mut l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [59, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,907667957179513571 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__11_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Grind_Action_intros___boxed as *const core::ffi::c_void, m_arity: 14, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [118, 97, 108, 117, 101, 32, 104, 97, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [116, 121, 112, 101, 32, 104, 97, 115, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19_value: crate::leanh::LeanStringObject<44> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [101, 108, 97, 98, 111, 114, 97, 116, 101, 100, 32, 116, 101, 114, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 96, 104, 97, 118, 101, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4_value) as *mut crate::leanh::LeanObject,13243635457614750868 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value) as *mut crate::leanh::LeanObject,5409699204079762053 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value) as *mut crate::leanh::LeanObject,4907018543776028915 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__6_value) as *mut crate::leanh::LeanObject,2725788849339585842 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__7_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10237484977487531059 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value) as *mut crate::leanh::LeanObject,4145789101286746142 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,13782581005565569772 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__10_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value) as *mut crate::leanh::LeanObject,4484422664080011241 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value) as *mut crate::leanh::LeanObject,5717024826078722151 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 118, 97, 108, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__13_value) as *mut crate::leanh::LeanObject,3496297410684516377 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [96, 102, 105, 110, 105, 115, 104, 96, 32, 102, 97, 105, 108, 101, 100, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 105, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,10861733237677782054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 97, 118, 101, 83, 105, 108, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__0_value) as *mut crate::leanh::LeanObject,4733526434027481274 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 72, 97, 118, 101, 83, 105, 108, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__0_value) as *mut crate::leanh::LeanObject,10196853978671031201 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(
    mut v_e_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_981_: u8 = 0;
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_987_: u8 = 0;
    let mut v_unused_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_967_ = l_Lean_Expr_hasMVar(v_e_964_);
                if v___x_967_ == 0 {
                    v___x_968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_968_, 0, v_e_964_);
                    return v___x_968_;
                } else {
                    v___x_969_ = lean_st_ref_get(v___y_965_);
                    v_mctx_970_ = crate::leanh::lean_ctor_get(v___x_969_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_970_);
                    crate::leanh::lean_dec(v___x_969_);
                    v___x_971_ = l_Lean_instantiateMVarsCore(v_mctx_970_, v_e_964_);
                    v_fst_972_ = crate::leanh::lean_ctor_get(v___x_971_, 0);
                    crate::leanh::lean_inc(v_fst_972_);
                    v_snd_973_ = crate::leanh::lean_ctor_get(v___x_971_, 1);
                    crate::leanh::lean_inc(v_snd_973_);
                    crate::leanh::lean_dec_ref(v___x_971_);
                    v___x_974_ = lean_st_ref_take(v___y_965_);
                    v_cache_975_ = crate::leanh::lean_ctor_get(v___x_974_, 1);
                    v_zetaDeltaFVarIds_976_ = crate::leanh::lean_ctor_get(v___x_974_, 2);
                    v_postponed_977_ = crate::leanh::lean_ctor_get(v___x_974_, 3);
                    v_diag_978_ = crate::leanh::lean_ctor_get(v___x_974_, 4);
                    v_isSharedCheck_987_ = (!crate::leanh::lean_is_exclusive(v___x_974_)) as u8;
                    if v_isSharedCheck_987_ == 0 {
                        v_unused_988_ = crate::leanh::lean_ctor_get(v___x_974_, 0);
                        crate::leanh::lean_dec(v_unused_988_);
                        v___x_980_ = v___x_974_;
                        v_isShared_981_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_978_);
                        crate::leanh::lean_inc(v_postponed_977_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_976_);
                        crate::leanh::lean_inc(v_cache_975_);
                        crate::leanh::lean_dec(v___x_974_);
                        v___x_980_ = crate::leanh::lean_box(0);
                        v_isShared_981_ = v_isSharedCheck_987_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_980_, 0, v_snd_973_);
                    v___x_983_ = v___x_980_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_986_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 0, v_snd_973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 1, v_cache_975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 2, v_zetaDeltaFVarIds_976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 3, v_postponed_977_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_986_, 4, v_diag_978_);
                    v___x_983_ = v_reuseFailAlloc_986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_984_ = lean_st_ref_set(v___y_965_, v___x_983_);
                v___x_985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_985_, 0, v_fst_972_);
                return v___x_985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg___boxed(
    mut v_e_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_e_989_, v___y_990_);
    crate::leanh::lean_dec(v___y_990_);
    return v_res_992_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(
    mut v_e_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
    mut v___y_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1003_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_e_993_, v___y_999_);
    return v___x_1003_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___boxed(
    mut v_e_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
    mut v___y_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v___y_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v___y_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1014_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0(v_e_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
    crate::leanh::lean_dec(v___y_1012_);
    crate::leanh::lean_dec_ref(v___y_1011_);
    crate::leanh::lean_dec(v___y_1010_);
    crate::leanh::lean_dec_ref(v___y_1009_);
    crate::leanh::lean_dec(v___y_1008_);
    crate::leanh::lean_dec_ref(v___y_1007_);
    crate::leanh::lean_dec(v___y_1006_);
    crate::leanh::lean_dec_ref(v___y_1005_);
    return v_res_1014_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(
    mut v_stx_1015_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1016_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1017_: u8,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
    mut v_a_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1027_ = 1;
                v___x_1028_ = l_Lean_Elab_Term_elabTerm(
                    v_stx_1015_,
                    v_expectedType_x3f_1016_,
                    v___x_1027_,
                    v___x_1027_,
                    v_a_1020_,
                    v_a_1021_,
                    v_a_1022_,
                    v_a_1023_,
                    v_a_1024_,
                    v_a_1025_,
                );
                if crate::leanh::lean_obj_tag(v___x_1028_) == 0 {
                    v_a_1029_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
                    crate::leanh::lean_inc(v_a_1029_);
                    crate::leanh::lean_dec_ref_known(v___x_1028_, 1);
                    v___x_1030_ = l_Lean_Elab_Term_PostponeBehavior_ofBool(v_mayPostpone_1017_);
                    v___x_1031_ = 0;
                    v___x_1032_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(
                        v___x_1030_,
                        v___x_1031_,
                        v_a_1020_,
                        v_a_1021_,
                        v_a_1022_,
                        v_a_1023_,
                        v_a_1024_,
                        v_a_1025_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1032_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1032_, 1);
                        v___x_1033_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v_a_1029_, v_a_1023_);
                        return v___x_1033_;
                    } else {
                        crate::leanh::lean_dec(v_a_1029_);
                        v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1032_, 0);
                        v_isSharedCheck_1041_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1032_)) as u8;
                        if v_isSharedCheck_1041_ == 0 {
                            v___x_1036_ = v___x_1032_;
                            v_isShared_1037_ = v_isSharedCheck_1041_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1034_);
                            crate::leanh::lean_dec(v___x_1032_);
                            v___x_1036_ = crate::leanh::lean_box(0);
                            v_isShared_1037_ = v_isSharedCheck_1041_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_1028_;
                }
            }
            1 => {
                if v_isShared_1037_ == 0 {
                    v___x_1039_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed(
    mut v_stx_1042_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1043_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mayPostpone_boxed_1054_: u8 = 0;
    let mut v_res_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_1054_ = (crate::leanh::lean_unbox(v_mayPostpone_1044_) as u8);
    v_res_1055_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(
        v_stx_1042_,
        v_expectedType_x3f_1043_,
        v_mayPostpone_boxed_1054_,
        v_a_1045_,
        v_a_1046_,
        v_a_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
    );
    crate::leanh::lean_dec(v_a_1052_);
    crate::leanh::lean_dec_ref(v_a_1051_);
    crate::leanh::lean_dec(v_a_1050_);
    crate::leanh::lean_dec_ref(v_a_1049_);
    crate::leanh::lean_dec(v_a_1048_);
    crate::leanh::lean_dec_ref(v_a_1047_);
    crate::leanh::lean_dec(v_a_1046_);
    crate::leanh::lean_dec_ref(v_a_1045_);
    return v_res_1055_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(
    mut v_a_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
    mut v___y_1059_: *mut crate::leanh::LeanObject,
    mut v___y_1060_: *mut crate::leanh::LeanObject,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1058_);
    crate::leanh::lean_inc_ref(v___y_1057_);
    v___x_1066_ = crate::leanh::lean_apply_2(v_a_1056_, v___y_1057_, v___y_1058_);
    v___x_1067_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v___x_1066_,
        v___y_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
        v___y_1063_,
        v___y_1064_,
    );
    return v___x_1067_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg___boxed(
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v___y_1069_: *mut crate::leanh::LeanObject,
    mut v___y_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v_a_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
    crate::leanh::lean_dec(v___y_1076_);
    crate::leanh::lean_dec_ref(v___y_1075_);
    crate::leanh::lean_dec(v___y_1074_);
    crate::leanh::lean_dec_ref(v___y_1073_);
    crate::leanh::lean_dec(v___y_1072_);
    crate::leanh::lean_dec_ref(v___y_1071_);
    crate::leanh::lean_dec(v___y_1070_);
    crate::leanh::lean_dec_ref(v___y_1069_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(
    mut v_00_u03b1_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
    mut v___y_1086_: *mut crate::leanh::LeanObject,
    mut v___y_1087_: *mut crate::leanh::LeanObject,
    mut v___y_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1090_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v_a_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
    return v___x_1090_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___boxed(
    mut v_00_u03b1_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
    mut v___y_1097_: *mut crate::leanh::LeanObject,
    mut v___y_1098_: *mut crate::leanh::LeanObject,
    mut v___y_1099_: *mut crate::leanh::LeanObject,
    mut v___y_1100_: *mut crate::leanh::LeanObject,
    mut v___y_1101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1102_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0(v_00_u03b1_1091_, v_a_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
    crate::leanh::lean_dec(v___y_1100_);
    crate::leanh::lean_dec_ref(v___y_1099_);
    crate::leanh::lean_dec(v___y_1098_);
    crate::leanh::lean_dec_ref(v___y_1097_);
    crate::leanh::lean_dec(v___y_1096_);
    crate::leanh::lean_dec_ref(v___y_1095_);
    crate::leanh::lean_dec(v___y_1094_);
    crate::leanh::lean_dec_ref(v___y_1093_);
    return v_res_1102_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(
    mut v_cond_1103_: u8,
    mut v_____r_1104_: *mut crate::leanh::LeanObject,
) -> u8 {
    if v_cond_1103_ == 0 {
        let mut v___x_1105_: u8 = 0;
        v___x_1105_ = 1;
        return v___x_1105_;
    } else {
        let mut v___x_1106_: u8 = 0;
        v___x_1106_ = 0;
        return v___x_1106_;
    }
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed(
    mut v_cond_1107_: *mut crate::leanh::LeanObject,
    mut v_____r_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cond_boxed_1109_: u8 = 0;
    let mut v_res_1110_: u8 = 0;
    let mut v_r_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_1109_ = (crate::leanh::lean_unbox(v_cond_1107_) as u8);
    v_res_1110_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_boxed_1109_, v_____r_1108_);
    v_r_1111_ = crate::leanh::lean_box((v_res_1110_) as usize);
    return v_r_1111_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(
    mut v___f_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: u8 = 0;
    v___x_1114_ = crate::leanh::lean_box(0);
    v___x_1115_ = crate::leanh::lean_apply_1(v___f_1112_, v___x_1114_);
    v___x_1116_ = (crate::leanh::lean_unbox(v___x_1115_) as u8);
    return v___x_1116_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed(
    mut v___f_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1119_: u8 = 0;
    let mut v_r_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1(v___f_1117_, v_x_1118_);
    v_r_1120_ = crate::leanh::lean_box((v_res_1119_) as usize);
    return v_r_1120_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(
    mut v_cond_1129_: u8,
    mut v_act_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_1143_: u8 = 0;
    let mut v_errToSorry_1144_: u8 = 0;
    let mut v_autoBoundImplicitContext_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_1146_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_1149_: u8 = 0;
    let mut v_heedElabAsElim_1150_: u8 = 0;
    let mut v_isNoncomputableSection_1151_: u8 = 0;
    let mut v_isMetaSection_1152_: u8 = 0;
    let mut v_ignoreTCFailures_1153_: u8 = 0;
    let mut v_inPattern_1154_: u8 = 0;
    let mut v_tacSnap_x3f_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_1156_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_1157_: u8 = 0;
    let mut v_checkDeprecated_1158_: u8 = 0;
    let mut v_fixedTermElabs_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1165_: u8 = 0;
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_old_x3f_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: u8 = 0;
    let mut v_val_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1179_: u8 = 0;
    let mut v_stx_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: u8 = 0;
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1140_ = crate::leanh::lean_ctor_get(v___y_1137_, 2);
                v_declName_x3f_1141_ = crate::leanh::lean_ctor_get(v___y_1133_, 0);
                v_macroStack_1142_ = crate::leanh::lean_ctor_get(v___y_1133_, 1);
                v_mayPostpone_1143_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_1144_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_1145_ = crate::leanh::lean_ctor_get(v___y_1133_, 2);
                v_autoBoundImplicitForbidden_1146_ = crate::leanh::lean_ctor_get(v___y_1133_, 3);
                v_sectionVars_1147_ = crate::leanh::lean_ctor_get(v___y_1133_, 4);
                v_sectionFVars_1148_ = crate::leanh::lean_ctor_get(v___y_1133_, 5);
                v_implicitLambda_1149_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_1150_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_1151_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_1152_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_ignoreTCFailures_1153_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                );
                v_inPattern_1154_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_1155_ = crate::leanh::lean_ctor_get(v___y_1133_, 6);
                v_saveRecAppSyntax_1156_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_1157_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_1158_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_1159_ = crate::leanh::lean_ctor_get(v___y_1133_, 7);
                if crate::leanh::lean_obj_tag(v_tacSnap_x3f_1155_) == 0 {
                    v___y_1161_ = v_tacSnap_x3f_1155_;
                    state = 1;
                    continue;
                } else {
                    v_val_1167_ = crate::leanh::lean_ctor_get(v_tacSnap_x3f_1155_, 0);
                    v_old_x3f_1168_ = crate::leanh::lean_ctor_get(v_val_1167_, 0);
                    v___x_1169_ = crate::leanh::lean_box((v_cond_1129_) as usize);
                    v___f_1170_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_1170_, 0, v___x_1169_);
                    if crate::leanh::lean_obj_tag(v_old_x3f_1168_) == 1 {
                        if v_cond_1129_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_1170_);
                            state = 3;
                            continue;
                        } else {
                            v_val_1174_ = crate::leanh::lean_ctor_get(v_old_x3f_1168_, 0);
                            v_map_1175_ = crate::leanh::lean_ctor_get(v_options_1140_, 0);
                            v___x_1176_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__3;
                            v___x_1177_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1175_, v___x_1176_);
                            if crate::leanh::lean_obj_tag(v___x_1177_) == 0 {
                                crate::leanh::lean_dec_ref(v___f_1170_);
                                state = 3;
                                continue;
                            } else {
                                v_val_1178_ = crate::leanh::lean_ctor_get(v___x_1177_, 0);
                                crate::leanh::lean_inc(v_val_1178_);
                                crate::leanh::lean_dec_ref_known(v___x_1177_, 1);
                                if crate::leanh::lean_obj_tag(v_val_1178_) == 1 {
                                    v_v_1179_ =
                                        crate::leanh::lean_ctor_get_uint8(v_val_1178_, 0 as u32);
                                    crate::leanh::lean_dec_ref_known(v_val_1178_, 0);
                                    if v_v_1179_ == 0 {
                                        crate::leanh::lean_dec_ref(v___f_1170_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_stx_1180_ = crate::leanh::lean_ctor_get(v_val_1174_, 0);
                                        v___f_1181_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                                        crate::leanh::lean_closure_set(v___f_1181_, 0, v___f_1170_);
                                        v___x_1182_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___closed__4;
                                        v___x_1183_ = crate::leanh::lean_box(0);
                                        v___x_1184_ = 0;
                                        crate::leanh::lean_inc(v_stx_1180_);
                                        v___x_1185_ = l_Lean_Syntax_formatStx(
                                            v_stx_1180_,
                                            v___x_1183_,
                                            v___x_1184_,
                                        );
                                        v___x_1186_ = l_Std_Format_defWidth;
                                        v___x_1187_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_1188_ = l_Std_Format_pretty(
                                            v___x_1185_,
                                            v___x_1186_,
                                            v___x_1187_,
                                            v___x_1187_,
                                        );
                                        v___x_1189_ = lean_string_append(v___x_1182_, v___x_1188_);
                                        crate::leanh::lean_dec_ref(v___x_1188_);
                                        v___x_1190_ = lean_dbg_trace(v___x_1189_, v___f_1181_);
                                        v___x_1191_ = (crate::leanh::lean_unbox(v___x_1190_) as u8);
                                        crate::leanh::lean_dec(v___x_1190_);
                                        v___y_1165_ = v___x_1191_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_1178_);
                                    crate::leanh::lean_dec_ref(v___f_1170_);
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___f_1170_);
                        v___x_1192_ = crate::leanh::lean_box(0);
                        v___x_1193_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_1129_, v___x_1192_);
                        v___y_1165_ = v___x_1193_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_fixedTermElabs_1159_);
                crate::leanh::lean_inc(v_sectionFVars_1148_);
                crate::leanh::lean_inc(v_sectionVars_1147_);
                crate::leanh::lean_inc_ref(v_autoBoundImplicitForbidden_1146_);
                crate::leanh::lean_inc(v_autoBoundImplicitContext_1145_);
                crate::leanh::lean_inc(v_macroStack_1142_);
                crate::leanh::lean_inc(v_declName_x3f_1141_);
                v___x_1162_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                crate::leanh::lean_ctor_set(v___x_1162_, 0, v_declName_x3f_1141_);
                crate::leanh::lean_ctor_set(v___x_1162_, 1, v_macroStack_1142_);
                crate::leanh::lean_ctor_set(v___x_1162_, 2, v_autoBoundImplicitContext_1145_);
                crate::leanh::lean_ctor_set(v___x_1162_, 3, v_autoBoundImplicitForbidden_1146_);
                crate::leanh::lean_ctor_set(v___x_1162_, 4, v_sectionVars_1147_);
                crate::leanh::lean_ctor_set(v___x_1162_, 5, v_sectionFVars_1148_);
                crate::leanh::lean_ctor_set(v___x_1162_, 6, v___y_1161_);
                crate::leanh::lean_ctor_set(v___x_1162_, 7, v_fixedTermElabs_1159_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v_mayPostpone_1143_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v_errToSorry_1144_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    v_implicitLambda_1149_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    v_heedElabAsElim_1150_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                    v_isNoncomputableSection_1151_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                    v_isMetaSection_1152_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                    v_ignoreTCFailures_1153_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                    v_inPattern_1154_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                    v_saveRecAppSyntax_1156_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                    v_holesAsSyntheticOpaque_1157_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                    v_checkDeprecated_1158_,
                );
                crate::leanh::lean_inc(v___y_1138_);
                crate::leanh::lean_inc_ref(v___y_1137_);
                crate::leanh::lean_inc(v___y_1136_);
                crate::leanh::lean_inc_ref(v___y_1135_);
                crate::leanh::lean_inc(v___y_1134_);
                crate::leanh::lean_inc(v___y_1132_);
                crate::leanh::lean_inc_ref(v___y_1131_);
                v___x_1163_ = crate::leanh::lean_apply_9(
                    v_act_1130_,
                    v___y_1131_,
                    v___y_1132_,
                    v___x_1162_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                    v___y_1138_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1163_;
            }
            2 => {
                if v___y_1165_ == 0 {
                    v___x_1166_ = crate::leanh::lean_box(0);
                    v___y_1161_ = v___x_1166_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_tacSnap_x3f_1155_);
                    v___y_1161_ = v_tacSnap_x3f_1155_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1172_ = crate::leanh::lean_box(0);
                v___x_1173_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___lam__0(v_cond_1129_, v___x_1172_);
                v___y_1165_ = v___x_1173_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg___boxed(
    mut v_cond_1194_: *mut crate::leanh::LeanObject,
    mut v_act_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
    mut v___y_1199_: *mut crate::leanh::LeanObject,
    mut v___y_1200_: *mut crate::leanh::LeanObject,
    mut v___y_1201_: *mut crate::leanh::LeanObject,
    mut v___y_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cond_boxed_1205_: u8 = 0;
    let mut v_res_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_1205_ = (crate::leanh::lean_unbox(v_cond_1194_) as u8);
    v_res_1206_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_boxed_1205_, v_act_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
    crate::leanh::lean_dec(v___y_1203_);
    crate::leanh::lean_dec_ref(v___y_1202_);
    crate::leanh::lean_dec(v___y_1201_);
    crate::leanh::lean_dec_ref(v___y_1200_);
    crate::leanh::lean_dec(v___y_1199_);
    crate::leanh::lean_dec_ref(v___y_1198_);
    crate::leanh::lean_dec(v___y_1197_);
    crate::leanh::lean_dec_ref(v___y_1196_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(
    mut v_00_u03b1_1207_: *mut crate::leanh::LeanObject,
    mut v_cond_1208_: u8,
    mut v_act_1209_: *mut crate::leanh::LeanObject,
    mut v___y_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v_cond_1208_, v_act_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
    return v___x_1219_;
}
pub unsafe fn l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___boxed(
    mut v_00_u03b1_1220_: *mut crate::leanh::LeanObject,
    mut v_cond_1221_: *mut crate::leanh::LeanObject,
    mut v_act_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
    mut v___y_1229_: *mut crate::leanh::LeanObject,
    mut v___y_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cond_boxed_1232_: u8 = 0;
    let mut v_res_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cond_boxed_1232_ = (crate::leanh::lean_unbox(v_cond_1221_) as u8);
    v_res_1233_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1(v_00_u03b1_1220_, v_cond_boxed_1232_, v_act_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
    crate::leanh::lean_dec(v___y_1230_);
    crate::leanh::lean_dec_ref(v___y_1229_);
    crate::leanh::lean_dec(v___y_1228_);
    crate::leanh::lean_dec_ref(v___y_1227_);
    crate::leanh::lean_dec(v___y_1226_);
    crate::leanh::lean_dec_ref(v___y_1225_);
    crate::leanh::lean_dec(v___y_1224_);
    crate::leanh::lean_dec_ref(v___y_1223_);
    return v_res_1233_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(
    mut v_stx_1234_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1235_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1236_: u8,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
    mut v___y_1240_: *mut crate::leanh::LeanObject,
    mut v___y_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toContext_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recover_1247_: u8 = 0;
    v_toContext_1246_ = crate::leanh::lean_ctor_get(v___y_1237_, 0);
    v_recover_1247_ = crate::leanh::lean_ctor_get_uint8(
        v_toContext_1246_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_recover_1247_ == 0 {
        let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1248_ = crate::leanh::lean_box((v_mayPostpone_1236_) as usize);
        v___x_1249_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go___boxed
                as *mut core::ffi::c_void,
            12,
            3,
        );
        crate::leanh::lean_closure_set(v___x_1249_, 0, v_stx_1234_);
        crate::leanh::lean_closure_set(v___x_1249_, 1, v_expectedType_x3f_1235_);
        crate::leanh::lean_closure_set(v___x_1249_, 2, v___x_1248_);
        v___x_1250_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__0___redArg(v___x_1249_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
        return v___x_1250_;
    } else {
        let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1251_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go(
            v_stx_1234_,
            v_expectedType_x3f_1235_,
            v_mayPostpone_1236_,
            v___y_1237_,
            v___y_1238_,
            v___y_1239_,
            v___y_1240_,
            v___y_1241_,
            v___y_1242_,
            v___y_1243_,
            v___y_1244_,
        );
        return v___x_1251_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed(
    mut v_stx_1252_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1253_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
    mut v___y_1258_: *mut crate::leanh::LeanObject,
    mut v___y_1259_: *mut crate::leanh::LeanObject,
    mut v___y_1260_: *mut crate::leanh::LeanObject,
    mut v___y_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v___y_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mayPostpone_boxed_1264_: u8 = 0;
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_1264_ = (crate::leanh::lean_unbox(v_mayPostpone_1254_) as u8);
    v_res_1265_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0(
            v_stx_1252_,
            v_expectedType_x3f_1253_,
            v_mayPostpone_boxed_1264_,
            v___y_1255_,
            v___y_1256_,
            v___y_1257_,
            v___y_1258_,
            v___y_1259_,
            v___y_1260_,
            v___y_1261_,
            v___y_1262_,
        );
    crate::leanh::lean_dec(v___y_1262_);
    crate::leanh::lean_dec_ref(v___y_1261_);
    crate::leanh::lean_dec(v___y_1260_);
    crate::leanh::lean_dec_ref(v___y_1259_);
    crate::leanh::lean_dec(v___y_1258_);
    crate::leanh::lean_dec_ref(v___y_1257_);
    crate::leanh::lean_dec(v___y_1256_);
    crate::leanh::lean_dec_ref(v___y_1255_);
    return v_res_1265_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(
    mut v_stx_1266_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1267_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1268_: u8,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1290_: u8 = 0;
    let mut v_cancelTk_x3f_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1292_: u8 = 0;
    let mut v_inheritedTraceOptions_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: u8 = 0;
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1278_ = crate::leanh::lean_ctor_get(v_a_1275_, 0);
    v_fileMap_1279_ = crate::leanh::lean_ctor_get(v_a_1275_, 1);
    v_options_1280_ = crate::leanh::lean_ctor_get(v_a_1275_, 2);
    v_currRecDepth_1281_ = crate::leanh::lean_ctor_get(v_a_1275_, 3);
    v_maxRecDepth_1282_ = crate::leanh::lean_ctor_get(v_a_1275_, 4);
    v_ref_1283_ = crate::leanh::lean_ctor_get(v_a_1275_, 5);
    v_currNamespace_1284_ = crate::leanh::lean_ctor_get(v_a_1275_, 6);
    v_openDecls_1285_ = crate::leanh::lean_ctor_get(v_a_1275_, 7);
    v_initHeartbeats_1286_ = crate::leanh::lean_ctor_get(v_a_1275_, 8);
    v_maxHeartbeats_1287_ = crate::leanh::lean_ctor_get(v_a_1275_, 9);
    v_quotContext_1288_ = crate::leanh::lean_ctor_get(v_a_1275_, 10);
    v_currMacroScope_1289_ = crate::leanh::lean_ctor_get(v_a_1275_, 11);
    v_diag_1290_ = crate::leanh::lean_ctor_get_uint8(
        v_a_1275_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1291_ = crate::leanh::lean_ctor_get(v_a_1275_, 12);
    v_suppressElabErrors_1292_ = crate::leanh::lean_ctor_get_uint8(
        v_a_1275_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1293_ = crate::leanh::lean_ctor_get(v_a_1275_, 13);
    v___x_1294_ = crate::leanh::lean_box((v_mayPostpone_1268_) as usize);
    crate::leanh::lean_inc(v_stx_1266_);
    v___f_1295_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1295_, 0, v_stx_1266_);
    crate::leanh::lean_closure_set(v___f_1295_, 1, v_expectedType_x3f_1267_);
    crate::leanh::lean_closure_set(v___f_1295_, 2, v___x_1294_);
    v___x_1296_ = 1;
    v___x_1297_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Grind_withMainContext___boxed as *mut core::ffi::c_void,
        11,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1297_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1297_, 1, v___f_1295_);
    v_ref_1298_ = l_Lean_replaceRef(v_stx_1266_, v_ref_1283_);
    crate::leanh::lean_dec(v_stx_1266_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1293_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1291_);
    crate::leanh::lean_inc(v_currMacroScope_1289_);
    crate::leanh::lean_inc(v_quotContext_1288_);
    crate::leanh::lean_inc(v_maxHeartbeats_1287_);
    crate::leanh::lean_inc(v_initHeartbeats_1286_);
    crate::leanh::lean_inc(v_openDecls_1285_);
    crate::leanh::lean_inc(v_currNamespace_1284_);
    crate::leanh::lean_inc(v_maxRecDepth_1282_);
    crate::leanh::lean_inc(v_currRecDepth_1281_);
    crate::leanh::lean_inc_ref(v_options_1280_);
    crate::leanh::lean_inc_ref(v_fileMap_1279_);
    crate::leanh::lean_inc_ref(v_fileName_1278_);
    v___x_1299_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1299_, 0, v_fileName_1278_);
    crate::leanh::lean_ctor_set(v___x_1299_, 1, v_fileMap_1279_);
    crate::leanh::lean_ctor_set(v___x_1299_, 2, v_options_1280_);
    crate::leanh::lean_ctor_set(v___x_1299_, 3, v_currRecDepth_1281_);
    crate::leanh::lean_ctor_set(v___x_1299_, 4, v_maxRecDepth_1282_);
    crate::leanh::lean_ctor_set(v___x_1299_, 5, v_ref_1298_);
    crate::leanh::lean_ctor_set(v___x_1299_, 6, v_currNamespace_1284_);
    crate::leanh::lean_ctor_set(v___x_1299_, 7, v_openDecls_1285_);
    crate::leanh::lean_ctor_set(v___x_1299_, 8, v_initHeartbeats_1286_);
    crate::leanh::lean_ctor_set(v___x_1299_, 9, v_maxHeartbeats_1287_);
    crate::leanh::lean_ctor_set(v___x_1299_, 10, v_quotContext_1288_);
    crate::leanh::lean_ctor_set(v___x_1299_, 11, v_currMacroScope_1289_);
    crate::leanh::lean_ctor_set(v___x_1299_, 12, v_cancelTk_x3f_1291_);
    crate::leanh::lean_ctor_set(v___x_1299_, 13, v_inheritedTraceOptions_1293_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1299_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1290_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1299_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1292_,
    );
    v___x_1300_ = l_Lean_Elab_Term_withoutTacticIncrementality___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_spec__1___redArg(v___x_1296_, v___x_1297_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v___x_1299_, v_a_1276_);
    crate::leanh::lean_dec_ref_known(v___x_1299_, 14);
    return v___x_1300_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm___boxed(
    mut v_stx_1301_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_1302_: *mut crate::leanh::LeanObject,
    mut v_mayPostpone_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
    mut v_a_1307_: *mut crate::leanh::LeanObject,
    mut v_a_1308_: *mut crate::leanh::LeanObject,
    mut v_a_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
    mut v_a_1311_: *mut crate::leanh::LeanObject,
    mut v_a_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mayPostpone_boxed_1313_: u8 = 0;
    let mut v_res_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mayPostpone_boxed_1313_ = (crate::leanh::lean_unbox(v_mayPostpone_1303_) as u8);
    v_res_1314_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(
        v_stx_1301_,
        v_expectedType_x3f_1302_,
        v_mayPostpone_boxed_1313_,
        v_a_1304_,
        v_a_1305_,
        v_a_1306_,
        v_a_1307_,
        v_a_1308_,
        v_a_1309_,
        v_a_1310_,
        v_a_1311_,
    );
    crate::leanh::lean_dec(v_a_1311_);
    crate::leanh::lean_dec_ref(v_a_1310_);
    crate::leanh::lean_dec(v_a_1309_);
    crate::leanh::lean_dec_ref(v_a_1308_);
    crate::leanh::lean_dec(v_a_1307_);
    crate::leanh::lean_dec_ref(v_a_1306_);
    crate::leanh::lean_dec(v_a_1305_);
    crate::leanh::lean_dec_ref(v_a_1304_);
    return v_res_1314_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1315_ = crate::leanh::lean_box(0);
    v___x_1316_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1317_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1317_, 0, v___x_1316_);
    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1315_);
    return v___x_1317_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___closed__0);
    v___x_1320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1320_, 0, v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg___boxed(
    mut v___y_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
    return v_res_1322_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(
    mut v_00_u03b1_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1333_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
    return v___x_1333_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___boxed(
    mut v_00_u03b1_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
    mut v___y_1336_: *mut crate::leanh::LeanObject,
    mut v___y_1337_: *mut crate::leanh::LeanObject,
    mut v___y_1338_: *mut crate::leanh::LeanObject,
    mut v___y_1339_: *mut crate::leanh::LeanObject,
    mut v___y_1340_: *mut crate::leanh::LeanObject,
    mut v___y_1341_: *mut crate::leanh::LeanObject,
    mut v___y_1342_: *mut crate::leanh::LeanObject,
    mut v___y_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0(v_00_u03b1_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
    crate::leanh::lean_dec(v___y_1342_);
    crate::leanh::lean_dec_ref(v___y_1341_);
    crate::leanh::lean_dec(v___y_1340_);
    crate::leanh::lean_dec_ref(v___y_1339_);
    crate::leanh::lean_dec(v___y_1338_);
    crate::leanh::lean_dec_ref(v___y_1337_);
    crate::leanh::lean_dec(v___y_1336_);
    crate::leanh::lean_dec_ref(v___y_1335_);
    return v_res_1344_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(
    mut v_msgData_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
    mut v___y_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = lean_st_ref_get(v___y_1349_);
    v_env_1352_ = crate::leanh::lean_ctor_get(v___x_1351_, 0);
    crate::leanh::lean_inc_ref(v_env_1352_);
    crate::leanh::lean_dec(v___x_1351_);
    v___x_1353_ = lean_st_ref_get(v___y_1347_);
    v_mctx_1354_ = crate::leanh::lean_ctor_get(v___x_1353_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1354_);
    crate::leanh::lean_dec(v___x_1353_);
    v_lctx_1355_ = crate::leanh::lean_ctor_get(v___y_1346_, 2);
    v_options_1356_ = crate::leanh::lean_ctor_get(v___y_1348_, 2);
    crate::leanh::lean_inc_ref(v_options_1356_);
    crate::leanh::lean_inc_ref(v_lctx_1355_);
    v___x_1357_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1357_, 0, v_env_1352_);
    crate::leanh::lean_ctor_set(v___x_1357_, 1, v_mctx_1354_);
    crate::leanh::lean_ctor_set(v___x_1357_, 2, v_lctx_1355_);
    crate::leanh::lean_ctor_set(v___x_1357_, 3, v_options_1356_);
    v___x_1358_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    crate::leanh::lean_ctor_set(v___x_1358_, 1, v_msgData_1345_);
    v___x_1359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1___boxed(
    mut v_msgData_1360_: *mut crate::leanh::LeanObject,
    mut v___y_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
    mut v___y_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msgData_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
    crate::leanh::lean_dec(v___y_1364_);
    crate::leanh::lean_dec_ref(v___y_1363_);
    crate::leanh::lean_dec(v___y_1362_);
    crate::leanh::lean_dec_ref(v___y_1361_);
    return v_res_1366_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(
    mut v_msg_1367_: *mut crate::leanh::LeanObject,
    mut v___y_1368_: *mut crate::leanh::LeanObject,
    mut v___y_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
    mut v___y_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1383_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1373_ = crate::leanh::lean_ctor_get(v___y_1370_, 5);
                v___x_1374_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1_spec__1(v_msg_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
                v_a_1375_ = crate::leanh::lean_ctor_get(v___x_1374_, 0);
                v_isSharedCheck_1383_ = (!crate::leanh::lean_is_exclusive(v___x_1374_)) as u8;
                if v_isSharedCheck_1383_ == 0 {
                    v___x_1377_ = v___x_1374_;
                    v_isShared_1378_ = v_isSharedCheck_1383_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1375_);
                    crate::leanh::lean_dec(v___x_1374_);
                    v___x_1377_ = crate::leanh::lean_box(0);
                    v_isShared_1378_ = v_isSharedCheck_1383_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1373_);
                v___x_1379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1379_, 0, v_ref_1373_);
                crate::leanh::lean_ctor_set(v___x_1379_, 1, v_a_1375_);
                if v_isShared_1378_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1377_, 1);
                    crate::leanh::lean_ctor_set(v___x_1377_, 0, v___x_1379_);
                    v___x_1381_ = v___x_1377_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
                    v___x_1381_ = v_reuseFailAlloc_1382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1381_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg___boxed(
    mut v_msg_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
    mut v___y_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
    crate::leanh::lean_dec(v___y_1388_);
    crate::leanh::lean_dec_ref(v___y_1387_);
    crate::leanh::lean_dec(v___y_1386_);
    crate::leanh::lean_dec_ref(v___y_1385_);
    return v_res_1390_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1397_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__7;
    v___x_1401_ = l_String_toRawSubstring_x27(v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1418_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__15;
    v___x_1419_ = l_Lean_stringToMessageData(v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__17;
    v___x_1422_ = l_Lean_stringToMessageData(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__19;
    v___x_1425_ = l_Lean_stringToMessageData(v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(
    mut v___x_1426_: u8,
    mut v_stx_1427_: *mut crate::leanh::LeanObject,
    mut v___x_1428_: *mut crate::leanh::LeanObject,
    mut v___x_1429_: *mut crate::leanh::LeanObject,
    mut v___x_1430_: *mut crate::leanh::LeanObject,
    mut v___y_1431_: *mut crate::leanh::LeanObject,
    mut v___y_1432_: *mut crate::leanh::LeanObject,
    mut v___y_1433_: *mut crate::leanh::LeanObject,
    mut v___y_1434_: *mut crate::leanh::LeanObject,
    mut v___y_1435_: *mut crate::leanh::LeanObject,
    mut v___y_1436_: *mut crate::leanh::LeanObject,
    mut v___y_1437_: *mut crate::leanh::LeanObject,
    mut v___y_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1489_: u8 = 0;
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_a_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1511_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v___y_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: u8 = 0;
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1426_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1430_);
                    crate::leanh::lean_dec_ref(v___x_1429_);
                    crate::leanh::lean_dec_ref(v___x_1428_);
                    v___x_1440_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
                    return v___x_1440_;
                } else {
                    v___x_1441_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1442_ = l_Lean_Syntax_getArg(v_stx_1427_, v___x_1441_);
                    v___x_1443_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__0;
                    v___x_1444_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__1;
                    crate::leanh::lean_inc_ref(v___x_1429_);
                    crate::leanh::lean_inc_ref(v___x_1428_);
                    v___x_1445_ =
                        l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___x_1443_, v___x_1444_);
                    crate::leanh::lean_inc(v___x_1442_);
                    v___x_1446_ = l_Lean_Syntax_isOfKind(v___x_1442_, v___x_1445_);
                    crate::leanh::lean_dec(v___x_1445_);
                    if v___x_1446_ == 0 {
                        crate::leanh::lean_dec(v___x_1442_);
                        crate::leanh::lean_dec_ref(v___x_1430_);
                        crate::leanh::lean_dec_ref(v___x_1429_);
                        crate::leanh::lean_dec_ref(v___x_1428_);
                        v___x_1447_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
                        return v___x_1447_;
                    } else {
                        v_ref_1448_ = crate::leanh::lean_ctor_get(v___y_1437_, 5);
                        v_quotContext_1449_ = crate::leanh::lean_ctor_get(v___y_1437_, 10);
                        v_currMacroScope_1450_ = crate::leanh::lean_ctor_get(v___y_1437_, 11);
                        v___x_1451_ = 0;
                        v___x_1452_ = l_Lean_SourceInfo_fromRef(v_ref_1448_, v___x_1451_);
                        crate::leanh::lean_inc_ref(v___x_1430_);
                        crate::leanh::lean_inc_ref(v___x_1429_);
                        crate::leanh::lean_inc_ref(v___x_1428_);
                        v___x_1453_ =
                            l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___x_1443_, v___x_1430_);
                        crate::leanh::lean_inc_n(v___x_1452_, 5);
                        v___x_1454_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1454_, 0, v___x_1452_);
                        crate::leanh::lean_ctor_set(v___x_1454_, 1, v___x_1430_);
                        v___x_1455_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__2;
                        v___x_1456_ =
                            l_Lean_Name_mkStr4(v___x_1428_, v___x_1429_, v___x_1443_, v___x_1455_);
                        v___x_1457_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__4;
                        v___x_1458_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__5);
                        v___x_1459_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1459_, 0, v___x_1452_);
                        crate::leanh::lean_ctor_set(v___x_1459_, 1, v___x_1457_);
                        crate::leanh::lean_ctor_set(v___x_1459_, 2, v___x_1458_);
                        v___x_1460_ = l_Lean_Syntax_node1(v___x_1452_, v___x_1456_, v___x_1459_);
                        v___x_1461_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__6;
                        v___x_1462_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1452_);
                        crate::leanh::lean_ctor_set(v___x_1462_, 1, v___x_1461_);
                        v___x_1463_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__8);
                        v___x_1464_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__9;
                        crate::leanh::lean_inc(v_currMacroScope_1450_);
                        crate::leanh::lean_inc(v_quotContext_1449_);
                        v___x_1465_ = l_Lean_addMacroScope(
                            v_quotContext_1449_,
                            v___x_1464_,
                            v_currMacroScope_1450_,
                        );
                        v___x_1466_ = crate::leanh::lean_box(0);
                        v___x_1467_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__13;
                        v___x_1468_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1468_, 0, v___x_1452_);
                        crate::leanh::lean_ctor_set(v___x_1468_, 1, v___x_1463_);
                        crate::leanh::lean_ctor_set(v___x_1468_, 2, v___x_1465_);
                        crate::leanh::lean_ctor_set(v___x_1468_, 3, v___x_1467_);
                        v___x_1469_ = l_Lean_Syntax_node5(
                            v___x_1452_,
                            v___x_1453_,
                            v___x_1454_,
                            v___x_1460_,
                            v___x_1442_,
                            v___x_1462_,
                            v___x_1468_,
                        );
                        v___x_1470_ = crate::leanh::lean_box(0);
                        v___x_1471_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(v___x_1469_, v___x_1470_, v___x_1451_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
                        if crate::leanh::lean_obj_tag(v___x_1471_) == 0 {
                            v_a_1472_ = crate::leanh::lean_ctor_get(v___x_1471_, 0);
                            crate::leanh::lean_inc(v_a_1472_);
                            crate::leanh::lean_dec_ref_known(v___x_1471_, 1);
                            if crate::leanh::lean_obj_tag(v_a_1472_) == 8 {
                                v_declName_1473_ = crate::leanh::lean_ctor_get(v_a_1472_, 0);
                                crate::leanh::lean_inc(v_declName_1473_);
                                v_type_1474_ = crate::leanh::lean_ctor_get(v_a_1472_, 1);
                                crate::leanh::lean_inc_ref(v_type_1474_);
                                v_value_1475_ = crate::leanh::lean_ctor_get(v_a_1472_, 2);
                                crate::leanh::lean_inc_ref(v_value_1475_);
                                crate::leanh::lean_dec_ref_known(v_a_1472_, 4);
                                v___x_1530_ = l_Lean_Expr_hasMVar(v_type_1474_);
                                if v___x_1530_ == 0 {
                                    v___y_1517_ = v___y_1431_;
                                    v___y_1518_ = v___y_1432_;
                                    v___y_1519_ = v___y_1433_;
                                    v___y_1520_ = v___y_1434_;
                                    v___y_1521_ = v___y_1435_;
                                    v___y_1522_ = v___y_1436_;
                                    v___y_1523_ = v___y_1437_;
                                    v___y_1524_ = v___y_1438_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_value_1475_);
                                    crate::leanh::lean_dec(v_declName_1473_);
                                    v___x_1531_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__18);
                                    v___x_1532_ = l_Lean_indentExpr(v_type_1474_);
                                    v___x_1533_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1533_, 0, v___x_1531_);
                                    crate::leanh::lean_ctor_set(v___x_1533_, 1, v___x_1532_);
                                    v___x_1534_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_1533_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
                                    return v___x_1534_;
                                }
                            } else {
                                v___x_1535_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__20);
                                v___x_1536_ = l_Lean_indentExpr(v_a_1472_);
                                v___x_1537_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1537_, 0, v___x_1535_);
                                crate::leanh::lean_ctor_set(v___x_1537_, 1, v___x_1536_);
                                v___x_1538_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_1537_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
                                return v___x_1538_;
                            }
                        } else {
                            v_a_1539_ = crate::leanh::lean_ctor_get(v___x_1471_, 0);
                            v_isSharedCheck_1546_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1471_)) as u8;
                            if v_isSharedCheck_1546_ == 0 {
                                v___x_1541_ = v___x_1471_;
                                v_isShared_1542_ = v_isSharedCheck_1546_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1539_);
                                crate::leanh::lean_dec(v___x_1471_);
                                v___x_1541_ = crate::leanh::lean_box(0);
                                v_isShared_1542_ = v_isSharedCheck_1546_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1483_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(
                    v___y_1478_,
                    v___y_1479_,
                    v___y_1480_,
                    v___y_1481_,
                    v___y_1482_,
                );
                if crate::leanh::lean_obj_tag(v___x_1483_) == 0 {
                    v_a_1484_ = crate::leanh::lean_ctor_get(v___x_1483_, 0);
                    crate::leanh::lean_inc(v_a_1484_);
                    crate::leanh::lean_dec_ref_known(v___x_1483_, 1);
                    v_toGoalState_1485_ = crate::leanh::lean_ctor_get(v_a_1484_, 0);
                    v_mvarId_1486_ = crate::leanh::lean_ctor_get(v_a_1484_, 1);
                    v_isSharedCheck_1507_ = (!crate::leanh::lean_is_exclusive(v_a_1484_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1488_ = v_a_1484_;
                        v_isShared_1489_ = v_isSharedCheck_1507_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_1486_);
                        crate::leanh::lean_inc(v_toGoalState_1485_);
                        crate::leanh::lean_dec(v_a_1484_);
                        v___x_1488_ = crate::leanh::lean_box(0);
                        v_isShared_1489_ = v_isSharedCheck_1507_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_1475_);
                    crate::leanh::lean_dec_ref(v_type_1474_);
                    crate::leanh::lean_dec(v_declName_1473_);
                    v_a_1508_ = crate::leanh::lean_ctor_get(v___x_1483_, 0);
                    v_isSharedCheck_1515_ = (!crate::leanh::lean_is_exclusive(v___x_1483_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1510_ = v___x_1483_;
                        v_isShared_1511_ = v_isSharedCheck_1515_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1508_);
                        crate::leanh::lean_dec(v___x_1483_);
                        v___x_1510_ = crate::leanh::lean_box(0);
                        v_isShared_1511_ = v_isSharedCheck_1515_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1490_ = l_Lean_MVarId_assert(
                    v_mvarId_1486_,
                    v_declName_1473_,
                    v_type_1474_,
                    v_value_1475_,
                    v___y_1479_,
                    v___y_1480_,
                    v___y_1481_,
                    v___y_1482_,
                );
                if crate::leanh::lean_obj_tag(v___x_1490_) == 0 {
                    v_a_1491_ = crate::leanh::lean_ctor_get(v___x_1490_, 0);
                    crate::leanh::lean_inc(v_a_1491_);
                    crate::leanh::lean_dec_ref_known(v___x_1490_, 1);
                    if v_isShared_1489_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1488_, 1, v_a_1491_);
                        v___x_1493_ = v___x_1488_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_toGoalState_1485_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_a_1491_);
                        v___x_1493_ = v_reuseFailAlloc_1498_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1488_);
                    crate::leanh::lean_dec_ref(v_toGoalState_1485_);
                    v_a_1499_ = crate::leanh::lean_ctor_get(v___x_1490_, 0);
                    v_isSharedCheck_1506_ = (!crate::leanh::lean_is_exclusive(v___x_1490_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1501_ = v___x_1490_;
                        v_isShared_1502_ = v_isSharedCheck_1506_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1499_);
                        crate::leanh::lean_dec(v___x_1490_);
                        v___x_1501_ = crate::leanh::lean_box(0);
                        v_isShared_1502_ = v_isSharedCheck_1506_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1494_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1494_, 0, v___x_1493_);
                crate::leanh::lean_ctor_set(v___x_1494_, 1, v___x_1466_);
                v___x_1495_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(
                    v___x_1494_,
                    v___y_1478_,
                    v___y_1479_,
                    v___y_1480_,
                    v___y_1481_,
                    v___y_1482_,
                );
                if crate::leanh::lean_obj_tag(v___x_1495_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1495_, 1);
                    v___x_1496_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
                    v___x_1497_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(
                        v___x_1496_,
                        v___y_1477_,
                        v___y_1478_,
                        v___y_1479_,
                        v___y_1480_,
                        v___y_1481_,
                        v___y_1482_,
                    );
                    return v___x_1497_;
                } else {
                    return v___x_1495_;
                }
            }
            4 => {
                if v_isShared_1502_ == 0 {
                    v___x_1504_ = v___x_1501_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1504_;
            }
            6 => {
                if v_isShared_1511_ == 0 {
                    v___x_1513_ = v___x_1510_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
                    v___x_1513_ = v_reuseFailAlloc_1514_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1513_;
            }
            8 => {
                v___x_1525_ = l_Lean_Expr_hasMVar(v_value_1475_);
                if v___x_1525_ == 0 {
                    v___y_1477_ = v___y_1517_;
                    v___y_1478_ = v___y_1518_;
                    v___y_1479_ = v___y_1521_;
                    v___y_1480_ = v___y_1522_;
                    v___y_1481_ = v___y_1523_;
                    v___y_1482_ = v___y_1524_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_type_1474_);
                    crate::leanh::lean_dec(v_declName_1473_);
                    v___x_1526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__16);
                    v___x_1527_ = l_Lean_indentExpr(v_value_1475_);
                    v___x_1528_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1526_);
                    crate::leanh::lean_ctor_set(v___x_1528_, 1, v___x_1527_);
                    v___x_1529_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
                    return v___x_1529_;
                }
            }
            9 => {
                if v_isShared_1542_ == 0 {
                    v___x_1544_ = v___x_1541_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed(
    mut v___x_1547_: *mut crate::leanh::LeanObject,
    mut v_stx_1548_: *mut crate::leanh::LeanObject,
    mut v___x_1549_: *mut crate::leanh::LeanObject,
    mut v___x_1550_: *mut crate::leanh::LeanObject,
    mut v___x_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
    mut v___y_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6380__boxed_1561_: u8 = 0;
    let mut v_res_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6380__boxed_1561_ = (crate::leanh::lean_unbox(v___x_1547_) as u8);
    v_res_1562_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0(
            v___x_6380__boxed_1561_,
            v_stx_1548_,
            v___x_1549_,
            v___x_1550_,
            v___x_1551_,
            v___y_1552_,
            v___y_1553_,
            v___y_1554_,
            v___y_1555_,
            v___y_1556_,
            v___y_1557_,
            v___y_1558_,
            v___y_1559_,
        );
    crate::leanh::lean_dec(v___y_1559_);
    crate::leanh::lean_dec_ref(v___y_1558_);
    crate::leanh::lean_dec(v___y_1557_);
    crate::leanh::lean_dec_ref(v___y_1556_);
    crate::leanh::lean_dec(v___y_1555_);
    crate::leanh::lean_dec_ref(v___y_1554_);
    crate::leanh::lean_dec(v___y_1553_);
    crate::leanh::lean_dec_ref(v___y_1552_);
    crate::leanh::lean_dec(v_stx_1548_);
    return v_res_1562_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(
    mut v_stx_1574_: *mut crate::leanh::LeanObject,
    mut v_a_1575_: *mut crate::leanh::LeanObject,
    mut v_a_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__0;
    v___x_1585_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__1;
    v___x_1586_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__4;
    v___x_1587_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
    crate::leanh::lean_inc(v_stx_1574_);
    v___x_1588_ = l_Lean_Syntax_isOfKind(v_stx_1574_, v___x_1587_);
    v___x_1589_ = crate::leanh::lean_box((v___x_1588_) as usize);
    v___y_1590_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___boxed
            as *mut core::ffi::c_void,
        14,
        5,
    );
    crate::leanh::lean_closure_set(v___y_1590_, 0, v___x_1589_);
    crate::leanh::lean_closure_set(v___y_1590_, 1, v_stx_1574_);
    crate::leanh::lean_closure_set(v___y_1590_, 2, v___x_1584_);
    crate::leanh::lean_closure_set(v___y_1590_, 3, v___x_1585_);
    crate::leanh::lean_closure_set(v___y_1590_, 4, v___x_1586_);
    v___x_1591_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_1590_,
        v_a_1575_,
        v_a_1576_,
        v_a_1577_,
        v_a_1578_,
        v_a_1579_,
        v_a_1580_,
        v_a_1581_,
        v_a_1582_,
    );
    return v___x_1591_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed(
    mut v_stx_1592_: *mut crate::leanh::LeanObject,
    mut v_a_1593_: *mut crate::leanh::LeanObject,
    mut v_a_1594_: *mut crate::leanh::LeanObject,
    mut v_a_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
    mut v_a_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
    mut v_a_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1602_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave(
        v_stx_1592_,
        v_a_1593_,
        v_a_1594_,
        v_a_1595_,
        v_a_1596_,
        v_a_1597_,
        v_a_1598_,
        v_a_1599_,
        v_a_1600_,
    );
    crate::leanh::lean_dec(v_a_1600_);
    crate::leanh::lean_dec_ref(v_a_1599_);
    crate::leanh::lean_dec(v_a_1598_);
    crate::leanh::lean_dec_ref(v_a_1597_);
    crate::leanh::lean_dec(v_a_1596_);
    crate::leanh::lean_dec_ref(v_a_1595_);
    crate::leanh::lean_dec(v_a_1594_);
    crate::leanh::lean_dec_ref(v_a_1593_);
    return v_res_1602_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(
    mut v_00_u03b1_1603_: *mut crate::leanh::LeanObject,
    mut v_msg_1604_: *mut crate::leanh::LeanObject,
    mut v___y_1605_: *mut crate::leanh::LeanObject,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v_msg_1604_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
    return v___x_1614_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___boxed(
    mut v_00_u03b1_1615_: *mut crate::leanh::LeanObject,
    mut v_msg_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
    mut v___y_1620_: *mut crate::leanh::LeanObject,
    mut v___y_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1(v_00_u03b1_1615_, v_msg_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
    crate::leanh::lean_dec(v___y_1624_);
    crate::leanh::lean_dec_ref(v___y_1623_);
    crate::leanh::lean_dec(v___y_1622_);
    crate::leanh::lean_dec_ref(v___y_1621_);
    crate::leanh::lean_dec(v___y_1620_);
    crate::leanh::lean_dec_ref(v___y_1619_);
    crate::leanh::lean_dec(v___y_1618_);
    crate::leanh::lean_dec_ref(v___y_1617_);
    return v_res_1626_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_1668_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___closed__5;
    v___x_1669_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___closed__14;
    v___x_1670_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1671_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1667_,
        v___x_1668_,
        v___x_1669_,
        v___x_1670_,
    );
    return v___x_1671_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1___boxed(
    mut v_a_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1673_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
    return v_res_1673_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__0;
    v___x_1676_ = l_Lean_stringToMessageData(v___x_1675_);
    return v___x_1676_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(
    mut v___x_1683_: u8,
    mut v_stx_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
    mut v___y_1687_: *mut crate::leanh::LeanObject,
    mut v___y_1688_: *mut crate::leanh::LeanObject,
    mut v___y_1689_: *mut crate::leanh::LeanObject,
    mut v___y_1690_: *mut crate::leanh::LeanObject,
    mut v___y_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1725_: u8 = 0;
    let mut v___y_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v_toGoalState_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut v_a_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1792_: u8 = 0;
    let mut v_a_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut v_reuseFailAlloc_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1803_: u8 = 0;
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1813_: u8 = 0;
    let mut v_a_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1817_: u8 = 0;
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_a_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut v___y_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_x3f_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_1683_ == 0 {
                    v___x_1694_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
                    return v___x_1694_;
                } else {
                    v___x_1695_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1858_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1859_ = l_Lean_Syntax_getArg(v_stx_1684_, v___x_1858_);
                    v___x_1860_ = l_Lean_Syntax_isNone(v___x_1859_);
                    if v___x_1860_ == 0 {
                        crate::leanh::lean_inc(v___x_1859_);
                        v___x_1861_ = l_Lean_Syntax_matchesNull(v___x_1859_, v___x_1858_);
                        if v___x_1861_ == 0 {
                            crate::leanh::lean_dec(v___x_1859_);
                            v___x_1862_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
                            return v___x_1862_;
                        } else {
                            v_id_x3f_1863_ = l_Lean_Syntax_getArg(v___x_1859_, v___x_1695_);
                            crate::leanh::lean_dec(v___x_1859_);
                            v___x_1864_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__5;
                            crate::leanh::lean_inc(v_id_x3f_1863_);
                            v___x_1865_ = l_Lean_Syntax_isOfKind(v_id_x3f_1863_, v___x_1864_);
                            if v___x_1865_ == 0 {
                                crate::leanh::lean_dec(v_id_x3f_1863_);
                                v___x_1866_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__0___redArg();
                                return v___x_1866_;
                            } else {
                                v___x_1867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1867_, 0, v_id_x3f_1863_);
                                v_id_x3f_1844_ = v___x_1867_;
                                v___y_1845_ = v___y_1685_;
                                v___y_1846_ = v___y_1686_;
                                v___y_1847_ = v___y_1687_;
                                v___y_1848_ = v___y_1688_;
                                v___y_1849_ = v___y_1689_;
                                v___y_1850_ = v___y_1690_;
                                v___y_1851_ = v___y_1691_;
                                v___y_1852_ = v___y_1692_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1859_);
                        v___x_1868_ = crate::leanh::lean_box(0);
                        v_id_x3f_1844_ = v___x_1868_;
                        v___y_1845_ = v___y_1685_;
                        v___y_1846_ = v___y_1686_;
                        v___y_1847_ = v___y_1687_;
                        v___y_1848_ = v___y_1688_;
                        v___y_1849_ = v___y_1689_;
                        v___y_1850_ = v___y_1690_;
                        v___y_1851_ = v___y_1691_;
                        v___y_1852_ = v___y_1692_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1709_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm_go_spec__0___redArg(v___y_1701_, v___y_1706_);
                v_a_1710_ = crate::leanh::lean_ctor_get(v___x_1709_, 0);
                crate::leanh::lean_inc(v_a_1710_);
                crate::leanh::lean_dec_ref(v___x_1709_);
                v___x_1711_ = l_Lean_MVarId_assert(
                    v___y_1699_,
                    v___y_1698_,
                    v___y_1702_,
                    v_a_1710_,
                    v___y_1705_,
                    v___y_1706_,
                    v___y_1707_,
                    v___y_1708_,
                );
                if crate::leanh::lean_obj_tag(v___x_1711_) == 0 {
                    v_a_1712_ = crate::leanh::lean_ctor_get(v___x_1711_, 0);
                    crate::leanh::lean_inc(v_a_1712_);
                    crate::leanh::lean_dec_ref_known(v___x_1711_, 1);
                    v___x_1713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1713_, 0, v___y_1697_);
                    crate::leanh::lean_ctor_set(v___x_1713_, 1, v_a_1712_);
                    v___x_1714_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1714_, 0, v___x_1713_);
                    crate::leanh::lean_ctor_set(v___x_1714_, 1, v___y_1700_);
                    v___x_1715_ =
                        l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_1714_, v___y_1704_);
                    if crate::leanh::lean_obj_tag(v___x_1715_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1715_, 1);
                        v___x_1716_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___lam__0___closed__14;
                        v___x_1717_ = l_Lean_Elab_Tactic_Grind_liftAction___redArg(
                            v___x_1716_,
                            v___y_1703_,
                            v___y_1704_,
                            v___y_1705_,
                            v___y_1706_,
                            v___y_1707_,
                            v___y_1708_,
                        );
                        return v___x_1717_;
                    } else {
                        return v___x_1715_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1700_);
                    crate::leanh::lean_dec_ref(v___y_1697_);
                    v_a_1718_ = crate::leanh::lean_ctor_get(v___x_1711_, 0);
                    v_isSharedCheck_1725_ = (!crate::leanh::lean_is_exclusive(v___x_1711_)) as u8;
                    if v_isSharedCheck_1725_ == 0 {
                        v___x_1720_ = v___x_1711_;
                        v_isShared_1721_ = v_isSharedCheck_1725_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1718_);
                        crate::leanh::lean_dec(v___x_1711_);
                        v___x_1720_ = crate::leanh::lean_box(0);
                        v_isShared_1721_ = v_isSharedCheck_1725_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1721_ == 0 {
                    v___x_1723_ = v___x_1720_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1723_;
            }
            4 => {
                v___x_1737_ = crate::leanh::lean_box(0);
                v___x_1738_ = 0;
                v___x_1739_ =
                    l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_elabTerm(
                        v___y_1734_,
                        v___x_1737_,
                        v___x_1738_,
                        v___y_1729_,
                        v___y_1735_,
                        v___y_1733_,
                        v___y_1732_,
                        v___y_1727_,
                        v___y_1731_,
                        v___y_1728_,
                        v___y_1730_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1739_) == 0 {
                    v_a_1740_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                    crate::leanh::lean_inc_n(v_a_1740_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1739_, 1);
                    v___x_1741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1741_, 0, v_a_1740_);
                    v___x_1742_ = 0;
                    v___x_1743_ = crate::leanh::lean_box(0);
                    v___x_1744_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_1741_,
                        v___x_1742_,
                        v___x_1743_,
                        v___y_1727_,
                        v___y_1731_,
                        v___y_1728_,
                        v___y_1730_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1744_) == 0 {
                        v_a_1745_ = crate::leanh::lean_ctor_get(v___x_1744_, 0);
                        crate::leanh::lean_inc(v_a_1745_);
                        crate::leanh::lean_dec_ref_known(v___x_1744_, 1);
                        v___x_1746_ = l_Lean_Elab_Tactic_Grind_getGoals___redArg(v___y_1735_);
                        if crate::leanh::lean_obj_tag(v___x_1746_) == 0 {
                            v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                            crate::leanh::lean_inc(v_a_1747_);
                            crate::leanh::lean_dec_ref_known(v___x_1746_, 1);
                            if crate::leanh::lean_obj_tag(v_a_1747_) == 1 {
                                v_head_1748_ = crate::leanh::lean_ctor_get(v_a_1747_, 0);
                                v_tail_1749_ = crate::leanh::lean_ctor_get(v_a_1747_, 1);
                                v_isSharedCheck_1804_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_1747_)) as u8;
                                if v_isSharedCheck_1804_ == 0 {
                                    v___x_1751_ = v_a_1747_;
                                    v_isShared_1752_ = v_isSharedCheck_1804_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_tail_1749_);
                                    crate::leanh::lean_inc(v_head_1748_);
                                    crate::leanh::lean_dec(v_a_1747_);
                                    v___x_1751_ = crate::leanh::lean_box(0);
                                    v_isShared_1752_ = v_isSharedCheck_1804_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1747_);
                                crate::leanh::lean_dec(v_a_1745_);
                                crate::leanh::lean_dec(v_a_1740_);
                                crate::leanh::lean_dec(v___y_1736_);
                                v___x_1805_ =
                                    l_Lean_Elab_Tactic_Grind_throwNoGoalsToBeSolved___redArg(
                                        v___y_1727_,
                                        v___y_1731_,
                                        v___y_1728_,
                                        v___y_1730_,
                                    );
                                return v___x_1805_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1745_);
                            crate::leanh::lean_dec(v_a_1740_);
                            crate::leanh::lean_dec(v___y_1736_);
                            v_a_1806_ = crate::leanh::lean_ctor_get(v___x_1746_, 0);
                            v_isSharedCheck_1813_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1746_)) as u8;
                            if v_isSharedCheck_1813_ == 0 {
                                v___x_1808_ = v___x_1746_;
                                v_isShared_1809_ = v_isSharedCheck_1813_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1806_);
                                crate::leanh::lean_dec(v___x_1746_);
                                v___x_1808_ = crate::leanh::lean_box(0);
                                v_isShared_1809_ = v_isSharedCheck_1813_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1740_);
                        crate::leanh::lean_dec(v___y_1736_);
                        v_a_1814_ = crate::leanh::lean_ctor_get(v___x_1744_, 0);
                        v_isSharedCheck_1821_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1744_)) as u8;
                        if v_isSharedCheck_1821_ == 0 {
                            v___x_1816_ = v___x_1744_;
                            v_isShared_1817_ = v_isSharedCheck_1821_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1814_);
                            crate::leanh::lean_dec(v___x_1744_);
                            v___x_1816_ = crate::leanh::lean_box(0);
                            v_isShared_1817_ = v_isSharedCheck_1821_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1736_);
                    v_a_1822_ = crate::leanh::lean_ctor_get(v___x_1739_, 0);
                    v_isSharedCheck_1829_ = (!crate::leanh::lean_is_exclusive(v___x_1739_)) as u8;
                    if v_isSharedCheck_1829_ == 0 {
                        v___x_1824_ = v___x_1739_;
                        v_isShared_1825_ = v_isSharedCheck_1829_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1822_);
                        crate::leanh::lean_dec(v___x_1739_);
                        v___x_1824_ = crate::leanh::lean_box(0);
                        v_isShared_1825_ = v_isSharedCheck_1829_;
                        state = 19;
                        continue;
                    }
                }
            }
            5 => {
                v_toGoalState_1753_ = crate::leanh::lean_ctor_get(v_head_1748_, 0);
                v_mvarId_1754_ = crate::leanh::lean_ctor_get(v_head_1748_, 1);
                v_isSharedCheck_1803_ = (!crate::leanh::lean_is_exclusive(v_head_1748_)) as u8;
                if v_isSharedCheck_1803_ == 0 {
                    v___x_1756_ = v_head_1748_;
                    v_isShared_1757_ = v_isSharedCheck_1803_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_1754_);
                    crate::leanh::lean_inc(v_toGoalState_1753_);
                    crate::leanh::lean_dec(v_head_1748_);
                    v___x_1756_ = crate::leanh::lean_box(0);
                    v_isShared_1757_ = v_isSharedCheck_1803_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1758_ = l_Lean_Expr_mvarId_x21(v_a_1745_);
                crate::leanh::lean_inc_ref(v_toGoalState_1753_);
                if v_isShared_1757_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1756_, 1, v___x_1758_);
                    v___x_1760_ = v___x_1756_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_toGoalState_1753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 1, v___x_1758_);
                    v___x_1760_ = v_reuseFailAlloc_1802_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1761_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v___x_1760_);
                if v_isShared_1752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1761_);
                    crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1760_);
                    v___x_1763_ = v___x_1751_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___x_1761_);
                    v___x_1763_ = v_reuseFailAlloc_1801_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1764_ = l_Lean_Elab_Tactic_Grind_setGoals___redArg(v___x_1763_, v___y_1735_);
                if crate::leanh::lean_obj_tag(v___x_1764_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1764_, 1);
                    v___x_1765_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_solve___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_1765_, 0, v___x_1760_);
                    v___x_1766_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(
                        v___x_1765_,
                        v___y_1729_,
                        v___y_1735_,
                        v___y_1727_,
                        v___y_1731_,
                        v___y_1728_,
                        v___y_1730_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1766_) == 0 {
                        v_a_1767_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                        crate::leanh::lean_inc(v_a_1767_);
                        crate::leanh::lean_dec_ref_known(v___x_1766_, 1);
                        if crate::leanh::lean_obj_tag(v_a_1767_) == 1 {
                            crate::leanh::lean_dec(v_mvarId_1754_);
                            crate::leanh::lean_dec_ref(v_toGoalState_1753_);
                            crate::leanh::lean_dec(v_tail_1749_);
                            crate::leanh::lean_dec(v_a_1745_);
                            crate::leanh::lean_dec(v_a_1740_);
                            crate::leanh::lean_dec(v___y_1736_);
                            v_params_1768_ = crate::leanh::lean_ctor_get(v___y_1729_, 4);
                            crate::leanh::lean_inc_ref(v_params_1768_);
                            v___x_1769_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Meta_Grind_mkResult___boxed as *mut core::ffi::c_void,
                                12,
                                2,
                            );
                            crate::leanh::lean_closure_set(v___x_1769_, 0, v_params_1768_);
                            crate::leanh::lean_closure_set(v___x_1769_, 1, v_a_1767_);
                            v___x_1770_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(
                                v___x_1769_,
                                v___y_1729_,
                                v___y_1735_,
                                v___y_1727_,
                                v___y_1731_,
                                v___y_1728_,
                                v___y_1730_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1770_) == 0 {
                                v_a_1771_ = crate::leanh::lean_ctor_get(v___x_1770_, 0);
                                crate::leanh::lean_inc(v_a_1771_);
                                crate::leanh::lean_dec_ref_known(v___x_1770_, 1);
                                v___x_1772_ = l_Lean_Meta_Grind_Result_toMessageData(
                                    v_a_1771_,
                                    v___y_1727_,
                                    v___y_1731_,
                                    v___y_1728_,
                                    v___y_1730_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1772_) == 0 {
                                    v_a_1773_ = crate::leanh::lean_ctor_get(v___x_1772_, 0);
                                    crate::leanh::lean_inc(v_a_1773_);
                                    crate::leanh::lean_dec_ref_known(v___x_1772_, 1);
                                    v___x_1774_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__1);
                                    v___x_1775_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                                    crate::leanh::lean_ctor_set(v___x_1775_, 1, v_a_1773_);
                                    v___x_1776_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave_spec__1___redArg(v___x_1775_, v___y_1727_, v___y_1731_, v___y_1728_, v___y_1730_);
                                    return v___x_1776_;
                                } else {
                                    v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1772_, 0);
                                    v_isSharedCheck_1784_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1772_)) as u8;
                                    if v_isSharedCheck_1784_ == 0 {
                                        v___x_1779_ = v___x_1772_;
                                        v_isShared_1780_ = v_isSharedCheck_1784_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1777_);
                                        crate::leanh::lean_dec(v___x_1772_);
                                        v___x_1779_ = crate::leanh::lean_box(0);
                                        v_isShared_1780_ = v_isSharedCheck_1784_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_1785_ = crate::leanh::lean_ctor_get(v___x_1770_, 0);
                                v_isSharedCheck_1792_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1770_)) as u8;
                                if v_isSharedCheck_1792_ == 0 {
                                    v___x_1787_ = v___x_1770_;
                                    v_isShared_1788_ = v_isSharedCheck_1792_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1785_);
                                    crate::leanh::lean_dec(v___x_1770_);
                                    v___x_1787_ = crate::leanh::lean_box(0);
                                    v_isShared_1788_ = v_isSharedCheck_1792_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1767_);
                            v___y_1697_ = v_toGoalState_1753_;
                            v___y_1698_ = v___y_1736_;
                            v___y_1699_ = v_mvarId_1754_;
                            v___y_1700_ = v_tail_1749_;
                            v___y_1701_ = v_a_1745_;
                            v___y_1702_ = v_a_1740_;
                            v___y_1703_ = v___y_1729_;
                            v___y_1704_ = v___y_1735_;
                            v___y_1705_ = v___y_1727_;
                            v___y_1706_ = v___y_1731_;
                            v___y_1707_ = v___y_1728_;
                            v___y_1708_ = v___y_1730_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_1754_);
                        crate::leanh::lean_dec_ref(v_toGoalState_1753_);
                        crate::leanh::lean_dec(v_tail_1749_);
                        crate::leanh::lean_dec(v_a_1745_);
                        crate::leanh::lean_dec(v_a_1740_);
                        crate::leanh::lean_dec(v___y_1736_);
                        v_a_1793_ = crate::leanh::lean_ctor_get(v___x_1766_, 0);
                        v_isSharedCheck_1800_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1766_)) as u8;
                        if v_isSharedCheck_1800_ == 0 {
                            v___x_1795_ = v___x_1766_;
                            v_isShared_1796_ = v_isSharedCheck_1800_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1793_);
                            crate::leanh::lean_dec(v___x_1766_);
                            v___x_1795_ = crate::leanh::lean_box(0);
                            v_isShared_1796_ = v_isSharedCheck_1800_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1760_);
                    crate::leanh::lean_dec(v_mvarId_1754_);
                    crate::leanh::lean_dec_ref(v_toGoalState_1753_);
                    crate::leanh::lean_dec(v_tail_1749_);
                    crate::leanh::lean_dec(v_a_1745_);
                    crate::leanh::lean_dec(v_a_1740_);
                    crate::leanh::lean_dec(v___y_1736_);
                    return v___x_1764_;
                }
            }
            9 => {
                if v_isShared_1780_ == 0 {
                    v___x_1782_ = v___x_1779_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1782_;
            }
            11 => {
                if v_isShared_1788_ == 0 {
                    v___x_1790_ = v___x_1787_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1791_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1790_;
            }
            13 => {
                if v_isShared_1796_ == 0 {
                    v___x_1798_ = v___x_1795_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
                    v___x_1798_ = v_reuseFailAlloc_1799_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1798_;
            }
            15 => {
                if v_isShared_1809_ == 0 {
                    v___x_1811_ = v___x_1808_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
                    v___x_1811_ = v_reuseFailAlloc_1812_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1811_;
            }
            17 => {
                if v_isShared_1817_ == 0 {
                    v___x_1819_ = v___x_1816_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1819_;
            }
            19 => {
                if v_isShared_1825_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
                    v___x_1827_ = v_reuseFailAlloc_1828_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1827_;
            }
            21 => {
                v___x_1841_ = l_Lean_Name_hasMacroScopes(v___y_1840_);
                if v___x_1841_ == 0 {
                    v___x_1842_ = l_Lean_Meta_Grind_markGrindName(v___y_1840_);
                    v___y_1727_ = v___y_1831_;
                    v___y_1728_ = v___y_1833_;
                    v___y_1729_ = v___y_1832_;
                    v___y_1730_ = v___y_1834_;
                    v___y_1731_ = v___y_1835_;
                    v___y_1732_ = v___y_1836_;
                    v___y_1733_ = v___y_1837_;
                    v___y_1734_ = v___y_1838_;
                    v___y_1735_ = v___y_1839_;
                    v___y_1736_ = v___x_1842_;
                    state = 4;
                    continue;
                } else {
                    v___y_1727_ = v___y_1831_;
                    v___y_1728_ = v___y_1833_;
                    v___y_1729_ = v___y_1832_;
                    v___y_1730_ = v___y_1834_;
                    v___y_1731_ = v___y_1835_;
                    v___y_1732_ = v___y_1836_;
                    v___y_1733_ = v___y_1837_;
                    v___y_1734_ = v___y_1838_;
                    v___y_1735_ = v___y_1839_;
                    v___y_1736_ = v___y_1840_;
                    state = 4;
                    continue;
                }
            }
            22 => {
                v___x_1853_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1854_ = l_Lean_Syntax_getArg(v_stx_1684_, v___x_1853_);
                if crate::leanh::lean_obj_tag(v_id_x3f_1844_) == 1 {
                    v_val_1855_ = crate::leanh::lean_ctor_get(v_id_x3f_1844_, 0);
                    crate::leanh::lean_inc(v_val_1855_);
                    crate::leanh::lean_dec_ref_known(v_id_x3f_1844_, 1);
                    v___x_1856_ = l_Lean_TSyntax_getId(v_val_1855_);
                    crate::leanh::lean_dec(v_val_1855_);
                    v___y_1831_ = v___y_1849_;
                    v___y_1832_ = v___y_1845_;
                    v___y_1833_ = v___y_1851_;
                    v___y_1834_ = v___y_1852_;
                    v___y_1835_ = v___y_1850_;
                    v___y_1836_ = v___y_1848_;
                    v___y_1837_ = v___y_1847_;
                    v___y_1838_ = v___x_1854_;
                    v___y_1839_ = v___y_1846_;
                    v___y_1840_ = v___x_1856_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_id_x3f_1844_);
                    v___x_1857_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___closed__3;
                    v___y_1831_ = v___y_1849_;
                    v___y_1832_ = v___y_1845_;
                    v___y_1833_ = v___y_1851_;
                    v___y_1834_ = v___y_1852_;
                    v___y_1835_ = v___y_1850_;
                    v___y_1836_ = v___y_1848_;
                    v___y_1837_ = v___y_1847_;
                    v___y_1838_ = v___x_1854_;
                    v___y_1839_ = v___y_1846_;
                    v___y_1840_ = v___x_1857_;
                    state = 21;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed(
    mut v___x_1869_: *mut crate::leanh::LeanObject,
    mut v_stx_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
    mut v___y_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3680__boxed_1880_: u8 = 0;
    let mut v_res_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3680__boxed_1880_ = (crate::leanh::lean_unbox(v___x_1869_) as u8);
    v_res_1881_ =
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0(
            v___x_3680__boxed_1880_,
            v_stx_1870_,
            v___y_1871_,
            v___y_1872_,
            v___y_1873_,
            v___y_1874_,
            v___y_1875_,
            v___y_1876_,
            v___y_1877_,
            v___y_1878_,
        );
    crate::leanh::lean_dec(v___y_1878_);
    crate::leanh::lean_dec_ref(v___y_1877_);
    crate::leanh::lean_dec(v___y_1876_);
    crate::leanh::lean_dec_ref(v___y_1875_);
    crate::leanh::lean_dec(v___y_1874_);
    crate::leanh::lean_dec_ref(v___y_1873_);
    crate::leanh::lean_dec(v___y_1872_);
    crate::leanh::lean_dec_ref(v___y_1871_);
    crate::leanh::lean_dec(v_stx_1870_);
    return v_res_1881_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(
    mut v_stx_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1;
    crate::leanh::lean_inc(v_stx_1889_);
    v___x_1900_ = l_Lean_Syntax_isOfKind(v_stx_1889_, v___x_1899_);
    v___x_1901_ = crate::leanh::lean_box((v___x_1900_) as usize);
    v___y_1902_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
    crate::leanh::lean_closure_set(v___y_1902_, 0, v___x_1901_);
    crate::leanh::lean_closure_set(v___y_1902_, 1, v_stx_1889_);
    v___x_1903_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_1902_,
        v_a_1890_,
        v_a_1891_,
        v_a_1892_,
        v_a_1893_,
        v_a_1894_,
        v_a_1895_,
        v_a_1896_,
        v_a_1897_,
    );
    return v___x_1903_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed(
    mut v_stx_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
    mut v_a_1909_: *mut crate::leanh::LeanObject,
    mut v_a_1910_: *mut crate::leanh::LeanObject,
    mut v_a_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
    mut v_a_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent(
        v_stx_1904_,
        v_a_1905_,
        v_a_1906_,
        v_a_1907_,
        v_a_1908_,
        v_a_1909_,
        v_a_1910_,
        v_a_1911_,
        v_a_1912_,
    );
    crate::leanh::lean_dec(v_a_1912_);
    crate::leanh::lean_dec_ref(v_a_1911_);
    crate::leanh::lean_dec(v_a_1910_);
    crate::leanh::lean_dec_ref(v_a_1909_);
    crate::leanh::lean_dec(v_a_1908_);
    crate::leanh::lean_dec_ref(v_a_1907_);
    crate::leanh::lean_dec(v_a_1906_);
    crate::leanh::lean_dec_ref(v_a_1905_);
    return v_res_1914_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_1921_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___closed__1;
    v___x_1922_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___closed__1;
    v___x_1923_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1924_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1920_,
        v___x_1921_,
        v___x_1922_,
        v___x_1923_,
    );
    return v___x_1924_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1___boxed(
    mut v_a_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
    return v_res_1926_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Have(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_SyntheticMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHave__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent___regBuiltin___private_Lean_Elab_Tactic_Grind_Have_0__Lean_Elab_Tactic_Grind_evalHaveSilent__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Have(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Have(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_SyntheticMVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Solve(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Have(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Have(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Have(builtin);
}
