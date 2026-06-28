// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.ShowState
// Imports: Lean.Elab.Tactic.Grind.Filter Lean.Meta.Tactic.Grind.PP Lean.Meta.Tactic.Grind.EMatchTheoremParam Lean.Meta.Tactic.Grind.Split
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_toArray___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    l_Lean_Elab_Tactic_Grind_evalGrindTactic, l_Lean_Elab_Tactic_Grind_getMainGoal___redArg,
    l_Lean_Elab_Tactic_Grind_grindTacElabAttribute, l_Lean_Elab_Tactic_Grind_liftGoalM___redArg,
    l_Lean_Elab_Tactic_Grind_liftGrindM___redArg,
    l_Lean_Elab_Tactic_Grind_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Filter::{
    initialize_Lean_Elab_Tactic_Grind_Filter, l_Lean_Elab_Tactic_Grind_elabFilter,
    runtime_initialize_Lean_Elab_Tactic_Grind_Filter,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_isFalse, l_Lean_Expr_isTrue, l_Lean_mkMVar,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getFalseExpr___redArg, l_Lean_Meta_Sym_getTrueExpr___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheoremParam::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
    l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Filter::{
    l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg,
    l_Lean_Meta_Grind_Filter_eval___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PP::{
    initialize_Lean_Meta_Tactic_Grind_PP, l_Lean_Meta_Grind_isSupportApp, l_Lean_Meta_Grind_ppEqc,
    l_Lean_Meta_Grind_ppExprArray, runtime_initialize_Lean_Meta_Tactic_Grind_PP,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Split::{
    initialize_Lean_Meta_Tactic_Grind_Split, l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Split,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_Goal_getEqc, l_Lean_Meta_Grind_Goal_getEqcs, l_Lean_Meta_Grind_anchorToString,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_string_dec_eq,
    lean_uint64_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64,
    lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint64, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 99, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__0_value) as *mut LeanObject,5835464875110000645 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [65, 115, 115, 101, 114, 116, 101, 100, 32, 102, 97, 99, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__3_value) as *mut LeanObject,13286986945483979944 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 32, 102, 97, 99, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [103, 114, 105, 110, 100, 70, 105, 108, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 104, 111, 119, 65, 115, 115, 101, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__3_value) as *mut LeanObject,9307343899468237075 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut LeanObject,5444244426488757208 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,5409699204079762053 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,4907018543776028915 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [83, 104, 111, 119, 83, 116, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__6_value) as *mut LeanObject,4973687763257006341 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__7_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,9400596968518456272 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,17122610932071288489 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0_value) as *mut LeanObject,4639418060637205991 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__10_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,7790049244909547814 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,7600593427671041812 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 65, 115, 115, 101, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__13_value) as *mut LeanObject,8525709122615365832 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 112, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__0_value) as *mut LeanObject,1388899078119845201 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 104, 111, 119, 84, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__0_value) as *mut LeanObject,13150684902857301386 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2_value) as *mut LeanObject,12189819440004302135 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 84, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__0_value) as *mut LeanObject,10096196651201499988 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 104, 111, 119, 70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__0_value) as *mut LeanObject,1698790517460571917 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__0_value) as *mut LeanObject,11062114385780800709 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 113, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__0_value) as *mut LeanObject,13700905132686059645 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [69, 113, 117, 105, 118, 97, 108, 101, 110, 99, 101, 32, 99, 108, 97, 115, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [111, 116, 104, 101, 114, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [110, 111, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 99, 101, 32, 99, 108, 97, 115, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 104, 111, 119, 69, 113, 99, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__0_value) as *mut LeanObject,15569771006456468598 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 69, 113, 99, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__0_value) as *mut LeanObject,18159781123131733934 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value: LeanStringObject<6> =
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
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value: LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2: f64 = 0.0;
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value: LeanStringObject<12> =
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
        m_data: [71, 114, 105, 110, 100, 32, 115, 116, 97, 116, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 104, 111, 119, 83, 116, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__0_value) as *mut LeanObject,10137114440480477384 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 83, 116, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__0_value) as *mut LeanObject,17909522331062329561 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 112, 108, 105, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__0_value) as *mut LeanObject,18188493160499796729 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [35, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 112, 108, 105, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__0_value) as *mut LeanObject,6944514875520371176 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [67, 97, 115, 101, 32, 115, 112, 108, 105, 116, 32, 99, 97, 110, 100, 105, 100, 97, 116, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [110, 111, 32, 99, 97, 115, 101, 32, 115, 112, 108, 105, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 104, 111, 119, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__0_value) as *mut LeanObject,9341503222632710516 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__0_value) as *mut LeanObject,15815244613950272402 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__0_value) as *mut LeanObject,11262269099723811472 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 109, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__0_value) as *mut LeanObject,9297490310868839267 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 111, 99, 97, 108, 32, 116, 104, 101, 111, 114, 101, 109, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 104, 111, 119, 76, 111, 99, 97, 108, 84, 104, 109, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__0_value) as *mut LeanObject,17299153005056664641 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 76, 111, 99, 97, 108, 84, 104, 109, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__2_value) as *mut LeanObject,15903457934410356249 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__0_value) as *mut LeanObject,11271821878211811031 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [103, 114, 105, 110, 100, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2_value) as *mut LeanObject,3168557723425139092 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__2_value) as *mut LeanObject,12547805878916670878 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 83, 104, 111, 119, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__0_value) as *mut LeanObject,5562123828496017471 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(
    mut v_filter_2946_: *mut LeanObject,
    mut v_as_2947_: *mut LeanObject,
    mut v_i_2948_: usize,
    mut v_stop_2949_: usize,
    mut v_b_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2954_: u8 = 0;
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: usize = 0;
    let mut v___x_2963_: u8 = 0;
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2968_: u8 = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2972_: u8 = 0;
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = lean_usize_dec_eq(v_i_2948_, v_stop_2949_);
                if v___x_2954_ == 0 {
                    v___x_2955_ = lean_array_uget_borrowed(v_as_2947_, v_i_2948_);
                    lean_inc(v_filter_2946_);
                    lean_inc(v___x_2955_);
                    v___x_2956_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v___x_2955_, v_filter_2946_, v___y_2951_, v___y_2952_);
                    if lean_obj_tag(v___x_2956_) == 0 {
                        v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
                        lean_inc(v_a_2957_);
                        lean_dec_ref_known(v___x_2956_, 1);
                        v___x_2963_ = (lean_unbox(v_a_2957_) as u8);
                        lean_dec(v_a_2957_);
                        if v___x_2963_ == 0 {
                            v_a_2959_ = v_b_2950_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v___x_2955_);
                            v___x_2964_ = lean_array_push(v_b_2950_, v___x_2955_);
                            v_a_2959_ = v___x_2964_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_2950_);
                        lean_dec(v_filter_2946_);
                        v_a_2965_ = lean_ctor_get(v___x_2956_, 0);
                        v_isSharedCheck_2972_ = (!lean_is_exclusive(v___x_2956_)) as u8;
                        if v_isSharedCheck_2972_ == 0 {
                            v___x_2967_ = v___x_2956_;
                            v_isShared_2968_ = v_isSharedCheck_2972_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2965_);
                            lean_dec(v___x_2956_);
                            v___x_2967_ = lean_box(0);
                            v_isShared_2968_ = v_isSharedCheck_2972_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_filter_2946_);
                    v___x_2973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2973_, 0, v_b_2950_);
                    return v___x_2973_;
                }
            }
            1 => {
                v___x_2960_ = 1usize;
                v___x_2961_ = lean_usize_add(v_i_2948_, v___x_2960_);
                v_i_2948_ = v___x_2961_;
                v_b_2950_ = v_a_2959_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2968_ == 0 {
                    v___x_2970_ = v___x_2967_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
                    v___x_2970_ = v_reuseFailAlloc_2971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg___boxed(
    mut v_filter_2974_: *mut LeanObject,
    mut v_as_2975_: *mut LeanObject,
    mut v_i_2976_: *mut LeanObject,
    mut v_stop_2977_: *mut LeanObject,
    mut v_b_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2982_: usize = 0;
    let mut v_stop_boxed_2983_: usize = 0;
    let mut v_res_2984_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2982_ = lean_unbox_usize(v_i_2976_);
    lean_dec(v_i_2976_);
    v_stop_boxed_2983_ = lean_unbox_usize(v_stop_2977_);
    lean_dec(v_stop_2977_);
    v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_2974_, v_as_2975_, v_i_boxed_2982_, v_stop_boxed_2983_, v_b_2978_, v___y_2979_, v___y_2980_);
    lean_dec(v___y_2980_);
    lean_dec(v___y_2979_);
    lean_dec_ref(v_as_2975_);
    return v_res_2984_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(
    mut v_filter_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facts_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: u8 = 0;
    v___x_2999_ = lean_st_ref_get(v___y_2988_);
    v_toGoalState_3000_ = lean_ctor_get(v___x_2999_, 0);
    lean_inc_ref(v_toGoalState_3000_);
    lean_dec(v___x_2999_);
    v_facts_3001_ = lean_ctor_get(v_toGoalState_3000_, 10);
    lean_inc_ref(v_facts_3001_);
    lean_dec_ref(v_toGoalState_3000_);
    v___x_3002_ = l_Lean_PersistentArray_toArray___redArg(v_facts_3001_);
    lean_dec_ref(v_facts_3001_);
    v___x_3003_ = lean_unsigned_to_nat(0);
    v___x_3004_ = lean_array_get_size(v___x_3002_);
    v___x_3005_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
    v___x_3006_ = lean_nat_dec_lt(v___x_3003_, v___x_3004_);
    if v___x_3006_ == 0 {
        let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_3002_);
        lean_dec(v_filter_2987_);
        v___x_3007_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3007_, 0, v___x_3005_);
        return v___x_3007_;
    } else {
        let mut v___x_3008_: u8 = 0;
        v___x_3008_ = lean_nat_dec_le(v___x_3004_, v___x_3004_);
        if v___x_3008_ == 0 {
            if v___x_3006_ == 0 {
                let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_3002_);
                lean_dec(v_filter_2987_);
                v___x_3009_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3009_, 0, v___x_3005_);
                return v___x_3009_;
            } else {
                let mut v___x_3010_: usize = 0;
                let mut v___x_3011_: usize = 0;
                let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
                v___x_3010_ = 0usize;
                v___x_3011_ = lean_usize_of_nat(v___x_3004_);
                v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_2987_, v___x_3002_, v___x_3010_, v___x_3011_, v___x_3005_, v___y_2988_, v___y_2995_);
                lean_dec_ref(v___x_3002_);
                return v___x_3012_;
            }
        } else {
            let mut v___x_3013_: usize = 0;
            let mut v___x_3014_: usize = 0;
            let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
            v___x_3013_ = 0usize;
            v___x_3014_ = lean_usize_of_nat(v___x_3004_);
            v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_2987_, v___x_3002_, v___x_3013_, v___x_3014_, v___x_3005_, v___y_2988_, v___y_2995_);
            lean_dec_ref(v___x_3002_);
            return v___x_3015_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed(
    mut v_filter_3016_: *mut LeanObject,
    mut v___y_3017_: *mut LeanObject,
    mut v___y_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
    mut v___y_3021_: *mut LeanObject,
    mut v___y_3022_: *mut LeanObject,
    mut v___y_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3028_: *mut LeanObject = core::ptr::null_mut();
    v_res_3028_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0(v_filter_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
    lean_dec(v___y_3026_);
    lean_dec_ref(v___y_3025_);
    lean_dec(v___y_3024_);
    lean_dec_ref(v___y_3023_);
    lean_dec(v___y_3022_);
    lean_dec_ref(v___y_3021_);
    lean_dec(v___y_3020_);
    lean_dec_ref(v___y_3019_);
    lean_dec(v___y_3018_);
    lean_dec(v___y_3017_);
    return v_res_3028_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(
    mut v_filter_3037_: *mut LeanObject,
    mut v_collapsed_3038_: u8,
    mut v_a_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
    mut v_a_3042_: *mut LeanObject,
    mut v_a_3043_: *mut LeanObject,
    mut v_a_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: u8 = 0;
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3067_: u8 = 0;
    let mut v_a_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3071_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3046_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
                lean_closure_set(v___f_3046_, 0, v_filter_3037_);
                v___x_3047_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(
                    v___f_3046_,
                    v_a_3039_,
                    v_a_3040_,
                    v_a_3041_,
                    v_a_3042_,
                    v_a_3043_,
                    v_a_3044_,
                );
                if lean_obj_tag(v___x_3047_) == 0 {
                    v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
                    v_isSharedCheck_3067_ = (!lean_is_exclusive(v___x_3047_)) as u8;
                    if v_isSharedCheck_3067_ == 0 {
                        v___x_3050_ = v___x_3047_;
                        v_isShared_3051_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3048_);
                        lean_dec(v___x_3047_);
                        v___x_3050_ = lean_box(0);
                        v_isShared_3051_ = v_isSharedCheck_3067_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3068_ = lean_ctor_get(v___x_3047_, 0);
                    v_isSharedCheck_3075_ = (!lean_is_exclusive(v___x_3047_)) as u8;
                    if v_isSharedCheck_3075_ == 0 {
                        v___x_3070_ = v___x_3047_;
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3068_);
                        lean_dec(v___x_3047_);
                        v___x_3070_ = lean_box(0);
                        v_isShared_3071_ = v_isSharedCheck_3075_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3052_ = lean_array_get_size(v_a_3048_);
                v___x_3053_ = lean_unsigned_to_nat(0);
                v___x_3054_ = lean_nat_dec_eq(v___x_3052_, v___x_3053_);
                if v___x_3054_ == 0 {
                    v___x_3055_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__1;
                    v___x_3056_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__2;
                    v___x_3057_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4;
                    v___x_3058_ = l_Lean_Meta_Grind_ppExprArray(
                        v___x_3055_,
                        v___x_3056_,
                        v_a_3048_,
                        v___x_3057_,
                        v_collapsed_3038_,
                    );
                    v___x_3059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3059_, 0, v___x_3058_);
                    if v_isShared_3051_ == 0 {
                        lean_ctor_set(v___x_3050_, 0, v___x_3059_);
                        v___x_3061_ = v___x_3050_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
                        v___x_3061_ = v_reuseFailAlloc_3062_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3048_);
                    v___x_3063_ = lean_box(0);
                    if v_isShared_3051_ == 0 {
                        lean_ctor_set(v___x_3050_, 0, v___x_3063_);
                        v___x_3065_ = v___x_3050_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
                        v___x_3065_ = v_reuseFailAlloc_3066_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3061_;
            }
            3 => {
                return v___x_3065_;
            }
            4 => {
                if v_isShared_3071_ == 0 {
                    v___x_3073_ = v___x_3070_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
                    v___x_3073_ = v_reuseFailAlloc_3074_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___boxed(
    mut v_filter_3076_: *mut LeanObject,
    mut v_collapsed_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
    mut v_a_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_3085_: u8 = 0;
    let mut v_res_3086_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3085_ = (lean_unbox(v_collapsed_3077_) as u8);
    v_res_3086_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_3076_, v_collapsed_boxed_3085_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    lean_dec(v_a_3081_);
    lean_dec_ref(v_a_3080_);
    lean_dec(v_a_3079_);
    lean_dec_ref(v_a_3078_);
    return v_res_3086_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(
    mut v_filter_3087_: *mut LeanObject,
    mut v_collapsed_3088_: u8,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    v___x_3098_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_3087_, v_collapsed_3088_, v_a_3089_, v_a_3090_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
    return v___x_3098_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___boxed(
    mut v_filter_3099_: *mut LeanObject,
    mut v_collapsed_3100_: *mut LeanObject,
    mut v_a_3101_: *mut LeanObject,
    mut v_a_3102_: *mut LeanObject,
    mut v_a_3103_: *mut LeanObject,
    mut v_a_3104_: *mut LeanObject,
    mut v_a_3105_: *mut LeanObject,
    mut v_a_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
    mut v_a_3108_: *mut LeanObject,
    mut v_a_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_3110_: u8 = 0;
    let mut v_res_3111_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_3110_ = (lean_unbox(v_collapsed_3100_) as u8);
    v_res_3111_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f(
            v_filter_3099_,
            v_collapsed_boxed_3110_,
            v_a_3101_,
            v_a_3102_,
            v_a_3103_,
            v_a_3104_,
            v_a_3105_,
            v_a_3106_,
            v_a_3107_,
            v_a_3108_,
        );
    lean_dec(v_a_3108_);
    lean_dec_ref(v_a_3107_);
    lean_dec(v_a_3106_);
    lean_dec_ref(v_a_3105_);
    lean_dec(v_a_3104_);
    lean_dec_ref(v_a_3103_);
    lean_dec(v_a_3102_);
    lean_dec_ref(v_a_3101_);
    return v_res_3111_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(
    mut v_filter_3112_: *mut LeanObject,
    mut v_as_3113_: *mut LeanObject,
    mut v_i_3114_: usize,
    mut v_stop_3115_: usize,
    mut v_b_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___redArg(v_filter_3112_, v_as_3113_, v_i_3114_, v_stop_3115_, v_b_3116_, v___y_3117_, v___y_3124_);
    return v___x_3128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0___boxed(
    mut v_filter_3129_: *mut LeanObject,
    mut v_as_3130_: *mut LeanObject,
    mut v_i_3131_: *mut LeanObject,
    mut v_stop_3132_: *mut LeanObject,
    mut v_b_3133_: *mut LeanObject,
    mut v___y_3134_: *mut LeanObject,
    mut v___y_3135_: *mut LeanObject,
    mut v___y_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3145_: usize = 0;
    let mut v_stop_boxed_3146_: usize = 0;
    let mut v_res_3147_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3145_ = lean_unbox_usize(v_i_3131_);
    lean_dec(v_i_3131_);
    v_stop_boxed_3146_ = lean_unbox_usize(v_stop_3132_);
    lean_dec(v_stop_3132_);
    v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f_spec__0(v_filter_3129_, v_as_3130_, v_i_boxed_3145_, v_stop_boxed_3146_, v_b_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
    lean_dec(v___y_3143_);
    lean_dec_ref(v___y_3142_);
    lean_dec(v___y_3141_);
    lean_dec_ref(v___y_3140_);
    lean_dec(v___y_3139_);
    lean_dec_ref(v___y_3138_);
    lean_dec(v___y_3137_);
    lean_dec_ref(v___y_3136_);
    lean_dec(v___y_3135_);
    lean_dec(v___y_3134_);
    lean_dec_ref(v_as_3130_);
    return v_res_3147_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    v___x_3148_ = lean_box(0);
    v___x_3149_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3150_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3150_, 0, v___x_3149_);
    lean_ctor_set(v___x_3150_, 1, v___x_3148_);
    return v___x_3150_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg()
-> *mut LeanObject {
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v___x_3152_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___closed__0);
    v___x_3153_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3153_, 0, v___x_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg___boxed(
    mut v___y_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3155_: *mut LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
    return v_res_3155_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(
    mut v_00_u03b1_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
    mut v___y_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    v___x_3166_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
    return v___x_3166_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___boxed(
    mut v_00_u03b1_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3177_: *mut LeanObject = core::ptr::null_mut();
    v_res_3177_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2(v_00_u03b1_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
    lean_dec(v___y_3175_);
    lean_dec_ref(v___y_3174_);
    lean_dec(v___y_3173_);
    lean_dec_ref(v___y_3172_);
    lean_dec(v___y_3171_);
    lean_dec_ref(v___y_3170_);
    lean_dec(v___y_3169_);
    lean_dec_ref(v___y_3168_);
    return v_res_3177_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(
    mut v_msgData_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    v___x_3184_ = lean_st_ref_get(v___y_3182_);
    v_env_3185_ = lean_ctor_get(v___x_3184_, 0);
    lean_inc_ref(v_env_3185_);
    lean_dec(v___x_3184_);
    v___x_3186_ = lean_st_ref_get(v___y_3180_);
    v_mctx_3187_ = lean_ctor_get(v___x_3186_, 0);
    lean_inc_ref(v_mctx_3187_);
    lean_dec(v___x_3186_);
    v_lctx_3188_ = lean_ctor_get(v___y_3179_, 2);
    v_options_3189_ = lean_ctor_get(v___y_3181_, 2);
    lean_inc_ref(v_options_3189_);
    lean_inc_ref(v_lctx_3188_);
    v___x_3190_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3190_, 0, v_env_3185_);
    lean_ctor_set(v___x_3190_, 1, v_mctx_3187_);
    lean_ctor_set(v___x_3190_, 2, v_lctx_3188_);
    lean_ctor_set(v___x_3190_, 3, v_options_3189_);
    v___x_3191_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3191_, 0, v___x_3190_);
    lean_ctor_set(v___x_3191_, 1, v_msgData_3178_);
    v___x_3192_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3192_, 0, v___x_3191_);
    return v___x_3192_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2___boxed(
    mut v_msgData_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3199_: *mut LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v_msgData_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
    lean_dec(v___y_3197_);
    lean_dec_ref(v___y_3196_);
    lean_dec(v___y_3195_);
    lean_dec_ref(v___y_3194_);
    return v_res_3199_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(
    mut v_msg_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3206_ = lean_ctor_get(v___y_3203_, 5);
                v___x_3207_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v_msg_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
                v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
                v_isSharedCheck_3216_ = (!lean_is_exclusive(v___x_3207_)) as u8;
                if v_isSharedCheck_3216_ == 0 {
                    v___x_3210_ = v___x_3207_;
                    v_isShared_3211_ = v_isSharedCheck_3216_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3208_);
                    lean_dec(v___x_3207_);
                    v___x_3210_ = lean_box(0);
                    v_isShared_3211_ = v_isSharedCheck_3216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3206_);
                v___x_3212_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3212_, 0, v_ref_3206_);
                lean_ctor_set(v___x_3212_, 1, v_a_3208_);
                if v_isShared_3211_ == 0 {
                    lean_ctor_set_tag(v___x_3210_, 1);
                    lean_ctor_set(v___x_3210_, 0, v___x_3212_);
                    v___x_3214_ = v___x_3210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
                    v___x_3214_ = v_reuseFailAlloc_3215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg___boxed(
    mut v_msg_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3223_: *mut LeanObject = core::ptr::null_mut();
    v_res_3223_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v_msg_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
    lean_dec(v___y_3221_);
    lean_dec_ref(v___y_3220_);
    lean_dec(v___y_3219_);
    lean_dec_ref(v___y_3218_);
    return v_res_3223_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(
    mut v_opts_3224_: *mut LeanObject,
    mut v_opt_3225_: *mut LeanObject,
) -> u8 {
    let mut v_name_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    v_name_3226_ = lean_ctor_get(v_opt_3225_, 0);
    v_defValue_3227_ = lean_ctor_get(v_opt_3225_, 1);
    v_map_3228_ = lean_ctor_get(v_opts_3224_, 0);
    v___x_3229_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3228_,
            v_name_3226_,
        );
    if lean_obj_tag(v___x_3229_) == 0 {
        let mut v___x_3230_: u8 = 0;
        v___x_3230_ = (lean_unbox(v_defValue_3227_) as u8);
        return v___x_3230_;
    } else {
        let mut v_val_3231_: *mut LeanObject = core::ptr::null_mut();
        v_val_3231_ = lean_ctor_get(v___x_3229_, 0);
        lean_inc(v_val_3231_);
        lean_dec_ref_known(v___x_3229_, 1);
        if lean_obj_tag(v_val_3231_) == 1 {
            let mut v_v_3232_: u8 = 0;
            v_v_3232_ = lean_ctor_get_uint8(v_val_3231_, 0 as u32);
            lean_dec_ref_known(v_val_3231_, 0);
            return v_v_3232_;
        } else {
            let mut v___x_3233_: u8 = 0;
            lean_dec(v_val_3231_);
            v___x_3233_ = (lean_unbox(v_defValue_3227_) as u8);
            return v___x_3233_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_opts_3234_: *mut LeanObject,
    mut v_opt_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3236_: u8 = 0;
    let mut v_r_3237_: *mut LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(v_opts_3234_, v_opt_3235_);
    lean_dec_ref(v_opt_3235_);
    lean_dec_ref(v_opts_3234_);
    v_r_3237_ = lean_box((v_res_3236_) as usize);
    return v_r_3237_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(
    mut v___y_3246_: u8,
    mut v_suppressElabErrors_3247_: u8,
    mut v_x_3248_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_3248_) == 1 {
        let mut v_pre_3249_: *mut LeanObject = core::ptr::null_mut();
        v_pre_3249_ = lean_ctor_get(v_x_3248_, 0);
        match lean_obj_tag(v_pre_3249_) {
            1 => {
                let mut v_pre_3250_: *mut LeanObject = core::ptr::null_mut();
                v_pre_3250_ = lean_ctor_get(v_pre_3249_, 0);
                match lean_obj_tag(v_pre_3250_) {
                    0 => {
                        let mut v_str_3251_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_3252_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3254_: u8 = 0;
                        v_str_3251_ = lean_ctor_get(v_x_3248_, 1);
                        v_str_3252_ = lean_ctor_get(v_pre_3249_, 1);
                        v___x_3253_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__0;
                        v___x_3254_ = lean_string_dec_eq(v_str_3252_, v___x_3253_);
                        if v___x_3254_ == 0 {
                            let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3256_: u8 = 0;
                            v___x_3255_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
                            v___x_3256_ = lean_string_dec_eq(v_str_3252_, v___x_3255_);
                            if v___x_3256_ == 0 {
                                return v___y_3246_;
                            } else {
                                let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3258_: u8 = 0;
                                v___x_3257_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__2;
                                v___x_3258_ = lean_string_dec_eq(v_str_3251_, v___x_3257_);
                                if v___x_3258_ == 0 {
                                    return v___y_3246_;
                                } else {
                                    return v_suppressElabErrors_3247_;
                                }
                            }
                        } else {
                            let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3260_: u8 = 0;
                            v___x_3259_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__3;
                            v___x_3260_ = lean_string_dec_eq(v_str_3251_, v___x_3259_);
                            if v___x_3260_ == 0 {
                                return v___y_3246_;
                            } else {
                                return v_suppressElabErrors_3247_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3261_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_3261_ = lean_ctor_get(v_pre_3250_, 0);
                        if lean_obj_tag(v_pre_3261_) == 0 {
                            let mut v_str_3262_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3263_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_3264_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_3266_: u8 = 0;
                            v_str_3262_ = lean_ctor_get(v_x_3248_, 1);
                            v_str_3263_ = lean_ctor_get(v_pre_3249_, 1);
                            v_str_3264_ = lean_ctor_get(v_pre_3250_, 1);
                            v___x_3265_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__4;
                            v___x_3266_ = lean_string_dec_eq(v_str_3264_, v___x_3265_);
                            if v___x_3266_ == 0 {
                                return v___y_3246_;
                            } else {
                                let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_3268_: u8 = 0;
                                v___x_3267_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__5;
                                v___x_3268_ = lean_string_dec_eq(v_str_3263_, v___x_3267_);
                                if v___x_3268_ == 0 {
                                    return v___y_3246_;
                                } else {
                                    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
                                    let mut v___x_3270_: u8 = 0;
                                    v___x_3269_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__6;
                                    v___x_3270_ = lean_string_dec_eq(v_str_3262_, v___x_3269_);
                                    if v___x_3270_ == 0 {
                                        return v___y_3246_;
                                    } else {
                                        return v_suppressElabErrors_3247_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3246_;
                        }
                    }
                    _ => {
                        return v___y_3246_;
                    }
                }
            }
            0 => {
                let mut v_str_3271_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3273_: u8 = 0;
                v_str_3271_ = lean_ctor_get(v_x_3248_, 1);
                v___x_3272_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__7;
                v___x_3273_ = lean_string_dec_eq(v_str_3271_, v___x_3272_);
                if v___x_3273_ == 0 {
                    return v___y_3246_;
                } else {
                    return v_suppressElabErrors_3247_;
                }
            }
            _ => {
                return v___y_3246_;
            }
        }
    } else {
        return v___y_3246_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed(
    mut v___y_3274_: *mut LeanObject,
    mut v_suppressElabErrors_3275_: *mut LeanObject,
    mut v_x_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6794__boxed_3277_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3278_: u8 = 0;
    let mut v_res_3279_: u8 = 0;
    let mut v_r_3280_: *mut LeanObject = core::ptr::null_mut();
    v___y_6794__boxed_3277_ = (lean_unbox(v___y_3274_) as u8);
    v_suppressElabErrors_boxed_3278_ = (lean_unbox(v_suppressElabErrors_3275_) as u8);
    v_res_3279_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0(v___y_6794__boxed_3277_, v_suppressElabErrors_boxed_3278_, v_x_3276_);
    lean_dec(v_x_3276_);
    v_r_3280_ = lean_box((v_res_3279_) as usize);
    return v_r_3280_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(
    mut v_ref_3282_: *mut LeanObject,
    mut v_msgData_3283_: *mut LeanObject,
    mut v_severity_3284_: u8,
    mut v_isSilent_3285_: u8,
    mut v___y_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3293_: u8 = 0;
    let mut v___y_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3297_: u8 = 0;
    let mut v___y_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v___y_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3329_: u8 = 0;
    let mut v___y_3330_: u8 = 0;
    let mut v___y_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3334_: u8 = 0;
    let mut v___y_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3351_: u8 = 0;
    let mut v___y_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3354_: u8 = 0;
    let mut v___y_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3356_: u8 = 0;
    let mut v___y_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3359_: u8 = 0;
    let mut v___y_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3365_: u8 = 0;
    let mut v___y_3366_: u8 = 0;
    let mut v___y_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3370_: u8 = 0;
    let mut v_ref_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: u8 = 0;
    let mut v___y_3377_: u8 = 0;
    let mut v___y_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3382_: u8 = 0;
    let mut v___y_3383_: u8 = 0;
    let mut v___y_3385_: u8 = 0;
    let mut v_fileName_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3390_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3375_ = 2;
                v___x_3400_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3284_, v___x_3375_);
                if v___x_3400_ == 0 {
                    v___y_3385_ = v___x_3400_;
                    state = 10;
                    continue;
                } else {
                    lean_inc_ref(v_msgData_3283_);
                    v___x_3401_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3283_);
                    v___y_3385_ = v___x_3401_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3301_ = lean_st_ref_take(v___y_3300_);
                v_currNamespace_3302_ = lean_ctor_get(v___y_3299_, 6);
                v_openDecls_3303_ = lean_ctor_get(v___y_3299_, 7);
                v_env_3304_ = lean_ctor_get(v___x_3301_, 0);
                v_nextMacroScope_3305_ = lean_ctor_get(v___x_3301_, 1);
                v_ngen_3306_ = lean_ctor_get(v___x_3301_, 2);
                v_auxDeclNGen_3307_ = lean_ctor_get(v___x_3301_, 3);
                v_traceState_3308_ = lean_ctor_get(v___x_3301_, 4);
                v_cache_3309_ = lean_ctor_get(v___x_3301_, 5);
                v_messages_3310_ = lean_ctor_get(v___x_3301_, 6);
                v_infoState_3311_ = lean_ctor_get(v___x_3301_, 7);
                v_snapshotTasks_3312_ = lean_ctor_get(v___x_3301_, 8);
                v_isSharedCheck_3326_ = (!lean_is_exclusive(v___x_3301_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v___x_3314_ = v___x_3301_;
                    v_isShared_3315_ = v_isSharedCheck_3326_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3312_);
                    lean_inc(v_infoState_3311_);
                    lean_inc(v_messages_3310_);
                    lean_inc(v_cache_3309_);
                    lean_inc(v_traceState_3308_);
                    lean_inc(v_auxDeclNGen_3307_);
                    lean_inc(v_ngen_3306_);
                    lean_inc(v_nextMacroScope_3305_);
                    lean_inc(v_env_3304_);
                    lean_dec(v___x_3301_);
                    v___x_3314_ = lean_box(0);
                    v_isShared_3315_ = v_isSharedCheck_3326_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_3303_);
                lean_inc(v_currNamespace_3302_);
                v___x_3316_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3316_, 0, v_currNamespace_3302_);
                lean_ctor_set(v___x_3316_, 1, v_openDecls_3303_);
                v___x_3317_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3317_, 0, v___x_3316_);
                lean_ctor_set(v___x_3317_, 1, v___y_3295_);
                lean_inc_ref(v___y_3298_);
                lean_inc_ref(v___y_3296_);
                v___x_3318_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_3318_, 0, v___y_3296_);
                lean_ctor_set(v___x_3318_, 1, v___y_3294_);
                lean_ctor_set(v___x_3318_, 2, v___y_3292_);
                lean_ctor_set(v___x_3318_, 3, v___y_3298_);
                lean_ctor_set(v___x_3318_, 4, v___x_3317_);
                lean_ctor_set_uint8(
                    v___x_3318_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_3293_,
                );
                lean_ctor_set_uint8(
                    v___x_3318_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_3297_,
                );
                lean_ctor_set_uint8(
                    v___x_3318_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3285_,
                );
                v___x_3319_ = l_Lean_MessageLog_add(v___x_3318_, v_messages_3310_);
                if v_isShared_3315_ == 0 {
                    lean_ctor_set(v___x_3314_, 6, v___x_3319_);
                    v___x_3321_ = v___x_3314_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_env_3304_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 1, v_nextMacroScope_3305_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 2, v_ngen_3306_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 3, v_auxDeclNGen_3307_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 4, v_traceState_3308_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 5, v_cache_3309_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 6, v___x_3319_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 7, v_infoState_3311_);
                    lean_ctor_set(v_reuseFailAlloc_3325_, 8, v_snapshotTasks_3312_);
                    v___x_3321_ = v_reuseFailAlloc_3325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3322_ = lean_st_ref_set(v___y_3300_, v___x_3321_);
                v___x_3323_ = lean_box(0);
                v___x_3324_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3324_, 0, v___x_3323_);
                return v___x_3324_;
            }
            4 => {
                v___x_3336_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3283_,
                    );
                v___x_3337_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1_spec__2(v___x_3336_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
                v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
                v_isSharedCheck_3351_ = (!lean_is_exclusive(v___x_3337_)) as u8;
                if v_isSharedCheck_3351_ == 0 {
                    v___x_3340_ = v___x_3337_;
                    v_isShared_3341_ = v_isSharedCheck_3351_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_3338_);
                    lean_dec(v___x_3337_);
                    v___x_3340_ = lean_box(0);
                    v_isShared_3341_ = v_isSharedCheck_3351_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_3332_, 2);
                v___x_3342_ = l_Lean_FileMap_toPosition(v___y_3332_, v___y_3331_);
                lean_dec(v___y_3331_);
                v___x_3343_ = l_Lean_FileMap_toPosition(v___y_3332_, v___y_3335_);
                lean_dec(v___y_3335_);
                v___x_3344_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3344_, 0, v___x_3343_);
                v___x_3345_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
                if v___y_3330_ == 0 {
                    lean_del_object(v___x_3340_);
                    lean_dec_ref(v___y_3328_);
                    v___y_3292_ = v___x_3344_;
                    v___y_3293_ = v___y_3329_;
                    v___y_3294_ = v___x_3342_;
                    v___y_3295_ = v_a_3338_;
                    v___y_3296_ = v___y_3333_;
                    v___y_3297_ = v___y_3334_;
                    v___y_3298_ = v___x_3345_;
                    v___y_3299_ = v___y_3288_;
                    v___y_3300_ = v___y_3289_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3338_);
                    v___x_3346_ = l_Lean_MessageData_hasTag(v___y_3328_, v_a_3338_);
                    if v___x_3346_ == 0 {
                        lean_dec_ref_known(v___x_3344_, 1);
                        lean_dec_ref(v___x_3342_);
                        lean_dec(v_a_3338_);
                        v___x_3347_ = lean_box(0);
                        if v_isShared_3341_ == 0 {
                            lean_ctor_set(v___x_3340_, 0, v___x_3347_);
                            v___x_3349_ = v___x_3340_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3347_);
                            v___x_3349_ = v_reuseFailAlloc_3350_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_3340_);
                        v___y_3292_ = v___x_3344_;
                        v___y_3293_ = v___y_3329_;
                        v___y_3294_ = v___x_3342_;
                        v___y_3295_ = v_a_3338_;
                        v___y_3296_ = v___y_3333_;
                        v___y_3297_ = v___y_3334_;
                        v___y_3298_ = v___x_3345_;
                        v___y_3299_ = v___y_3288_;
                        v___y_3300_ = v___y_3289_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3349_;
            }
            7 => {
                v___x_3361_ = l_Lean_Syntax_getTailPos_x3f(v___y_3355_, v___y_3354_);
                lean_dec(v___y_3355_);
                if lean_obj_tag(v___x_3361_) == 0 {
                    lean_inc(v___y_3360_);
                    v___y_3328_ = v___y_3353_;
                    v___y_3329_ = v___y_3354_;
                    v___y_3330_ = v___y_3356_;
                    v___y_3331_ = v___y_3360_;
                    v___y_3332_ = v___y_3357_;
                    v___y_3333_ = v___y_3358_;
                    v___y_3334_ = v___y_3359_;
                    v___y_3335_ = v___y_3360_;
                    state = 4;
                    continue;
                } else {
                    v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
                    lean_inc(v_val_3362_);
                    lean_dec_ref_known(v___x_3361_, 1);
                    v___y_3328_ = v___y_3353_;
                    v___y_3329_ = v___y_3354_;
                    v___y_3330_ = v___y_3356_;
                    v___y_3331_ = v___y_3360_;
                    v___y_3332_ = v___y_3357_;
                    v___y_3333_ = v___y_3358_;
                    v___y_3334_ = v___y_3359_;
                    v___y_3335_ = v_val_3362_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3371_ = l_Lean_replaceRef(v_ref_3282_, v___y_3369_);
                v___x_3372_ = l_Lean_Syntax_getPos_x3f(v_ref_3371_, v___y_3365_);
                if lean_obj_tag(v___x_3372_) == 0 {
                    v___x_3373_ = lean_unsigned_to_nat(0);
                    v___y_3353_ = v___y_3364_;
                    v___y_3354_ = v___y_3365_;
                    v___y_3355_ = v_ref_3371_;
                    v___y_3356_ = v___y_3366_;
                    v___y_3357_ = v___y_3367_;
                    v___y_3358_ = v___y_3368_;
                    v___y_3359_ = v___y_3370_;
                    v___y_3360_ = v___x_3373_;
                    state = 7;
                    continue;
                } else {
                    v_val_3374_ = lean_ctor_get(v___x_3372_, 0);
                    lean_inc(v_val_3374_);
                    lean_dec_ref_known(v___x_3372_, 1);
                    v___y_3353_ = v___y_3364_;
                    v___y_3354_ = v___y_3365_;
                    v___y_3355_ = v_ref_3371_;
                    v___y_3356_ = v___y_3366_;
                    v___y_3357_ = v___y_3367_;
                    v___y_3358_ = v___y_3368_;
                    v___y_3359_ = v___y_3370_;
                    v___y_3360_ = v_val_3374_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3383_ == 0 {
                    v___y_3364_ = v___y_3381_;
                    v___y_3365_ = v___y_3382_;
                    v___y_3366_ = v___y_3377_;
                    v___y_3367_ = v___y_3378_;
                    v___y_3368_ = v___y_3379_;
                    v___y_3369_ = v___y_3380_;
                    v___y_3370_ = v_severity_3284_;
                    state = 8;
                    continue;
                } else {
                    v___y_3364_ = v___y_3381_;
                    v___y_3365_ = v___y_3382_;
                    v___y_3366_ = v___y_3377_;
                    v___y_3367_ = v___y_3378_;
                    v___y_3368_ = v___y_3379_;
                    v___y_3369_ = v___y_3380_;
                    v___y_3370_ = v___x_3375_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3385_ == 0 {
                    v_fileName_3386_ = lean_ctor_get(v___y_3288_, 0);
                    v_fileMap_3387_ = lean_ctor_get(v___y_3288_, 1);
                    v_options_3388_ = lean_ctor_get(v___y_3288_, 2);
                    v_ref_3389_ = lean_ctor_get(v___y_3288_, 5);
                    v_suppressElabErrors_3390_ = lean_ctor_get_uint8(
                        v___y_3288_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3391_ = lean_box((v___y_3385_) as usize);
                    v___x_3392_ = lean_box((v_suppressElabErrors_3390_) as usize);
                    v___f_3393_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_3393_, 0, v___x_3391_);
                    lean_closure_set(v___f_3393_, 1, v___x_3392_);
                    v___x_3394_ = 1;
                    v___x_3395_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3284_, v___x_3394_);
                    if v___x_3395_ == 0 {
                        v___y_3377_ = v_suppressElabErrors_3390_;
                        v___y_3378_ = v_fileMap_3387_;
                        v___y_3379_ = v_fileName_3386_;
                        v___y_3380_ = v_ref_3389_;
                        v___y_3381_ = v___f_3393_;
                        v___y_3382_ = v___y_3385_;
                        v___y_3383_ = v___x_3395_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3396_ = l_Lean_warningAsError;
                        v___x_3397_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2_spec__5(v_options_3388_, v___x_3396_);
                        v___y_3377_ = v_suppressElabErrors_3390_;
                        v___y_3378_ = v_fileMap_3387_;
                        v___y_3379_ = v_fileName_3386_;
                        v___y_3380_ = v_ref_3389_;
                        v___y_3381_ = v___f_3393_;
                        v___y_3382_ = v___y_3385_;
                        v___y_3383_ = v___x_3397_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msgData_3283_);
                    v___x_3398_ = lean_box(0);
                    v___x_3399_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3399_, 0, v___x_3398_);
                    return v___x_3399_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_3402_: *mut LeanObject,
    mut v_msgData_3403_: *mut LeanObject,
    mut v_severity_3404_: *mut LeanObject,
    mut v_isSilent_3405_: *mut LeanObject,
    mut v___y_3406_: *mut LeanObject,
    mut v___y_3407_: *mut LeanObject,
    mut v___y_3408_: *mut LeanObject,
    mut v___y_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3411_: u8 = 0;
    let mut v_isSilent_boxed_3412_: u8 = 0;
    let mut v_res_3413_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3411_ = (lean_unbox(v_severity_3404_) as u8);
    v_isSilent_boxed_3412_ = (lean_unbox(v_isSilent_3405_) as u8);
    v_res_3413_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_3402_, v_msgData_3403_, v_severity_boxed_3411_, v_isSilent_boxed_3412_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
    lean_dec(v___y_3409_);
    lean_dec_ref(v___y_3408_);
    lean_dec(v___y_3407_);
    lean_dec_ref(v___y_3406_);
    lean_dec(v_ref_3402_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(
    mut v_msgData_3414_: *mut LeanObject,
    mut v_severity_3415_: u8,
    mut v_isSilent_3416_: u8,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3426_ = lean_ctor_get(v___y_3423_, 5);
    v___x_3427_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_3426_, v_msgData_3414_, v_severity_3415_, v_isSilent_3416_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0___boxed(
    mut v_msgData_3428_: *mut LeanObject,
    mut v_severity_3429_: *mut LeanObject,
    mut v_isSilent_3430_: *mut LeanObject,
    mut v___y_3431_: *mut LeanObject,
    mut v___y_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3440_: u8 = 0;
    let mut v_isSilent_boxed_3441_: u8 = 0;
    let mut v_res_3442_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3440_ = (lean_unbox(v_severity_3429_) as u8);
    v_isSilent_boxed_3441_ = (lean_unbox(v_isSilent_3430_) as u8);
    v_res_3442_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(v_msgData_3428_, v_severity_boxed_3440_, v_isSilent_boxed_3441_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
    lean_dec(v___y_3438_);
    lean_dec_ref(v___y_3437_);
    lean_dec(v___y_3436_);
    lean_dec_ref(v___y_3435_);
    lean_dec(v___y_3434_);
    lean_dec_ref(v___y_3433_);
    lean_dec(v___y_3432_);
    lean_dec_ref(v___y_3431_);
    return v_res_3442_;
}
pub unsafe fn l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(
    mut v_msgData_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
    mut v___y_3446_: *mut LeanObject,
    mut v___y_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    v___x_3453_ = 0;
    v___x_3454_ = 0;
    v___x_3455_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0(v_msgData_3443_, v___x_3453_, v___x_3454_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
    return v___x_3455_;
}
pub unsafe fn l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0___boxed(
    mut v_msgData_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
    mut v___y_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3466_: *mut LeanObject = core::ptr::null_mut();
    v_res_3466_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_msgData_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_);
    lean_dec(v___y_3464_);
    lean_dec_ref(v___y_3463_);
    lean_dec(v___y_3462_);
    lean_dec_ref(v___y_3461_);
    lean_dec(v___y_3460_);
    lean_dec_ref(v___y_3459_);
    lean_dec(v___y_3458_);
    lean_dec_ref(v___y_3457_);
    return v_res_3466_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    v___x_3468_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__0;
    v___x_3469_ = l_Lean_stringToMessageData(v___x_3468_);
    return v___x_3469_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(
    mut v___x_3471_: u8,
    mut v_stx_3472_: *mut LeanObject,
    mut v___x_3473_: *mut LeanObject,
    mut v___x_3474_: *mut LeanObject,
    mut v___x_3475_: *mut LeanObject,
    mut v___x_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_x3f_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3512_: u8 = 0;
    let mut v_a_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3520_: u8 = 0;
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_3471_ == 0 {
                    lean_dec_ref(v___x_3476_);
                    lean_dec_ref(v___x_3475_);
                    lean_dec_ref(v___x_3474_);
                    lean_dec_ref(v___x_3473_);
                    v___x_3521_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_3521_;
                } else {
                    v___x_3522_ = lean_unsigned_to_nat(1);
                    v___x_3523_ = l_Lean_Syntax_getArg(v_stx_3472_, v___x_3522_);
                    v___x_3524_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2;
                    v___x_3525_ = l_Lean_Name_mkStr5(
                        v___x_3473_,
                        v___x_3474_,
                        v___x_3475_,
                        v___x_3476_,
                        v___x_3524_,
                    );
                    lean_inc(v___x_3523_);
                    v___x_3526_ = l_Lean_Syntax_isOfKind(v___x_3523_, v___x_3525_);
                    lean_dec(v___x_3525_);
                    if v___x_3526_ == 0 {
                        lean_dec(v___x_3523_);
                        v___x_3527_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_3527_;
                    } else {
                        v___x_3528_ = lean_unsigned_to_nat(0);
                        v___x_3529_ = l_Lean_Syntax_getArg(v___x_3523_, v___x_3528_);
                        lean_dec(v___x_3523_);
                        v___x_3530_ = l_Lean_Syntax_isNone(v___x_3529_);
                        if v___x_3530_ == 0 {
                            lean_inc(v___x_3529_);
                            v___x_3531_ = l_Lean_Syntax_matchesNull(v___x_3529_, v___x_3522_);
                            if v___x_3531_ == 0 {
                                lean_dec(v___x_3529_);
                                v___x_3532_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                                return v___x_3532_;
                            } else {
                                v_filter_x3f_3533_ = l_Lean_Syntax_getArg(v___x_3529_, v___x_3528_);
                                lean_dec(v___x_3529_);
                                v___x_3534_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3534_, 0, v_filter_x3f_3533_);
                                v_filter_x3f_3487_ = v___x_3534_;
                                v___y_3488_ = v___y_3477_;
                                v___y_3489_ = v___y_3478_;
                                v___y_3490_ = v___y_3479_;
                                v___y_3491_ = v___y_3480_;
                                v___y_3492_ = v___y_3481_;
                                v___y_3493_ = v___y_3482_;
                                v___y_3494_ = v___y_3483_;
                                v___y_3495_ = v___y_3484_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3529_);
                            v___x_3535_ = lean_box(0);
                            v_filter_x3f_3487_ = v___x_3535_;
                            v___y_3488_ = v___y_3477_;
                            v___y_3489_ = v___y_3478_;
                            v___y_3490_ = v___y_3479_;
                            v___y_3491_ = v___y_3480_;
                            v___y_3492_ = v___y_3481_;
                            v___y_3493_ = v___y_3482_;
                            v___y_3494_ = v___y_3483_;
                            v___y_3495_ = v___y_3484_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3496_ = l_Lean_Elab_Tactic_Grind_elabFilter(
                    v_filter_x3f_3487_,
                    v___y_3488_,
                    v___y_3489_,
                    v___y_3490_,
                    v___y_3491_,
                    v___y_3492_,
                    v___y_3493_,
                    v___y_3494_,
                    v___y_3495_,
                );
                if lean_obj_tag(v___x_3496_) == 0 {
                    v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
                    lean_inc(v_a_3497_);
                    lean_dec_ref_known(v___x_3496_, 1);
                    v___x_3498_ = 0;
                    v___x_3499_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_a_3497_, v___x_3498_, v___y_3488_, v___y_3489_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
                    if lean_obj_tag(v___x_3499_) == 0 {
                        v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
                        lean_inc(v_a_3500_);
                        lean_dec_ref_known(v___x_3499_, 1);
                        if lean_obj_tag(v_a_3500_) == 1 {
                            v_val_3501_ = lean_ctor_get(v_a_3500_, 0);
                            lean_inc(v_val_3501_);
                            lean_dec_ref_known(v_a_3500_, 1);
                            v___x_3502_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_3501_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
                            return v___x_3502_;
                        } else {
                            lean_dec(v_a_3500_);
                            v___x_3503_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__1);
                            v___x_3504_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_3503_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
                            return v___x_3504_;
                        }
                    } else {
                        v_a_3505_ = lean_ctor_get(v___x_3499_, 0);
                        v_isSharedCheck_3512_ = (!lean_is_exclusive(v___x_3499_)) as u8;
                        if v_isSharedCheck_3512_ == 0 {
                            v___x_3507_ = v___x_3499_;
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3505_);
                            lean_dec(v___x_3499_);
                            v___x_3507_ = lean_box(0);
                            v_isShared_3508_ = v_isSharedCheck_3512_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_3513_ = lean_ctor_get(v___x_3496_, 0);
                    v_isSharedCheck_3520_ = (!lean_is_exclusive(v___x_3496_)) as u8;
                    if v_isSharedCheck_3520_ == 0 {
                        v___x_3515_ = v___x_3496_;
                        v_isShared_3516_ = v_isSharedCheck_3520_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3513_);
                        lean_dec(v___x_3496_);
                        v___x_3515_ = lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3520_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3508_ == 0 {
                    v___x_3510_ = v___x_3507_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
                    v___x_3510_ = v_reuseFailAlloc_3511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3510_;
            }
            4 => {
                if v_isShared_3516_ == 0 {
                    v___x_3518_ = v___x_3515_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3518_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed(
    mut v___x_3536_: *mut LeanObject,
    mut v_stx_3537_: *mut LeanObject,
    mut v___x_3538_: *mut LeanObject,
    mut v___x_3539_: *mut LeanObject,
    mut v___x_3540_: *mut LeanObject,
    mut v___x_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
    mut v___y_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7143__boxed_3551_: u8 = 0;
    let mut v_res_3552_: *mut LeanObject = core::ptr::null_mut();
    v___x_7143__boxed_3551_ = (lean_unbox(v___x_3536_) as u8);
    v_res_3552_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0(v___x_7143__boxed_3551_, v_stx_3537_, v___x_3538_, v___x_3539_, v___x_3540_, v___x_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
    lean_dec(v___y_3549_);
    lean_dec_ref(v___y_3548_);
    lean_dec(v___y_3547_);
    lean_dec_ref(v___y_3546_);
    lean_dec(v___y_3545_);
    lean_dec_ref(v___y_3544_);
    lean_dec(v___y_3543_);
    lean_dec_ref(v___y_3542_);
    lean_dec(v_stx_3537_);
    return v_res_3552_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(
    mut v_stx_3563_: *mut LeanObject,
    mut v_a_3564_: *mut LeanObject,
    mut v_a_3565_: *mut LeanObject,
    mut v_a_3566_: *mut LeanObject,
    mut v_a_3567_: *mut LeanObject,
    mut v_a_3568_: *mut LeanObject,
    mut v_a_3569_: *mut LeanObject,
    mut v_a_3570_: *mut LeanObject,
    mut v_a_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: u8 = 0;
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    v___x_3573_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0;
    v___x_3574_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1;
    v___x_3575_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
    v___x_3576_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2;
    v___x_3577_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4;
    lean_inc(v_stx_3563_);
    v___x_3578_ = l_Lean_Syntax_isOfKind(v_stx_3563_, v___x_3577_);
    v___x_3579_ = lean_box((v___x_3578_) as usize);
    v___y_3580_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___boxed as *mut core::ffi::c_void, 15, 6);
    lean_closure_set(v___y_3580_, 0, v___x_3579_);
    lean_closure_set(v___y_3580_, 1, v_stx_3563_);
    lean_closure_set(v___y_3580_, 2, v___x_3573_);
    lean_closure_set(v___y_3580_, 3, v___x_3574_);
    lean_closure_set(v___y_3580_, 4, v___x_3575_);
    lean_closure_set(v___y_3580_, 5, v___x_3576_);
    v___x_3581_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_3580_,
        v_a_3564_,
        v_a_3565_,
        v_a_3566_,
        v_a_3567_,
        v_a_3568_,
        v_a_3569_,
        v_a_3570_,
        v_a_3571_,
    );
    return v___x_3581_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed(
    mut v_stx_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
    mut v_a_3584_: *mut LeanObject,
    mut v_a_3585_: *mut LeanObject,
    mut v_a_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
    mut v_a_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3592_: *mut LeanObject = core::ptr::null_mut();
    v_res_3592_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted(
            v_stx_3582_,
            v_a_3583_,
            v_a_3584_,
            v_a_3585_,
            v_a_3586_,
            v_a_3587_,
            v_a_3588_,
            v_a_3589_,
            v_a_3590_,
        );
    lean_dec(v_a_3590_);
    lean_dec_ref(v_a_3589_);
    lean_dec(v_a_3588_);
    lean_dec_ref(v_a_3587_);
    lean_dec(v_a_3586_);
    lean_dec_ref(v_a_3585_);
    lean_dec(v_a_3584_);
    lean_dec_ref(v_a_3583_);
    return v_res_3592_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(
    mut v_00_u03b1_3593_: *mut LeanObject,
    mut v_msg_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    v___x_3604_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v_msg_3594_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
    return v___x_3604_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___boxed(
    mut v_00_u03b1_3605_: *mut LeanObject,
    mut v_msg_3606_: *mut LeanObject,
    mut v___y_3607_: *mut LeanObject,
    mut v___y_3608_: *mut LeanObject,
    mut v___y_3609_: *mut LeanObject,
    mut v___y_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
    mut v___y_3613_: *mut LeanObject,
    mut v___y_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3616_: *mut LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1(v_00_u03b1_3605_, v_msg_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
    lean_dec(v___y_3614_);
    lean_dec_ref(v___y_3613_);
    lean_dec(v___y_3612_);
    lean_dec_ref(v___y_3611_);
    lean_dec(v___y_3610_);
    lean_dec_ref(v___y_3609_);
    lean_dec(v___y_3608_);
    lean_dec_ref(v___y_3607_);
    return v_res_3616_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(
    mut v_ref_3617_: *mut LeanObject,
    mut v_msgData_3618_: *mut LeanObject,
    mut v_severity_3619_: u8,
    mut v_isSilent_3620_: u8,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_3617_, v_msgData_3618_, v_severity_3619_, v_isSilent_3620_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
    return v___x_3630_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___boxed(
    mut v_ref_3631_: *mut LeanObject,
    mut v_msgData_3632_: *mut LeanObject,
    mut v_severity_3633_: *mut LeanObject,
    mut v_isSilent_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
    mut v___y_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_3644_: u8 = 0;
    let mut v_isSilent_boxed_3645_: u8 = 0;
    let mut v_res_3646_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_3644_ = (lean_unbox(v_severity_3633_) as u8);
    v_isSilent_boxed_3645_ = (lean_unbox(v_isSilent_3634_) as u8);
    v_res_3646_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2(v_ref_3631_, v_msgData_3632_, v_severity_boxed_3644_, v_isSilent_boxed_3645_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
    lean_dec(v___y_3642_);
    lean_dec_ref(v___y_3641_);
    lean_dec(v___y_3640_);
    lean_dec_ref(v___y_3639_);
    lean_dec(v___y_3638_);
    lean_dec_ref(v___y_3637_);
    lean_dec(v___y_3636_);
    lean_dec_ref(v___y_3635_);
    lean_dec(v_ref_3631_);
    return v_res_3646_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1()
-> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_3688_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__4;
    v___x_3689_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___closed__14;
    v___x_3690_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_3691_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3687_,
        v___x_3688_,
        v___x_3689_,
        v___x_3690_,
    );
    return v___x_3691_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1___boxed(
    mut v_a_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3693_: *mut LeanObject = core::ptr::null_mut();
    v_res_3693_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
    return v_res_3693_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(
    mut v_filter_3694_: *mut LeanObject,
    mut v_as_3695_: *mut LeanObject,
    mut v_i_3696_: usize,
    mut v_stop_3697_: usize,
    mut v_b_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: usize = 0;
    let mut v___x_3705_: usize = 0;
    let mut v___x_3707_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: u8 = 0;
    let mut v___x_3715_: u8 = 0;
    let mut v_a_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v_a_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3721_: u8 = 0;
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3725_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3707_ = lean_usize_dec_eq(v_i_3696_, v_stop_3697_);
                if v___x_3707_ == 0 {
                    v___x_3708_ = lean_array_uget_borrowed(v_as_3695_, v_i_3696_);
                    lean_inc(v_filter_3694_);
                    lean_inc(v___x_3708_);
                    v___x_3711_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v___x_3708_, v_filter_3694_, v___y_3699_, v___y_3700_);
                    if lean_obj_tag(v___x_3711_) == 0 {
                        v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
                        lean_inc(v_a_3712_);
                        lean_dec_ref_known(v___x_3711_, 1);
                        v___x_3713_ = (lean_unbox(v_a_3712_) as u8);
                        lean_dec(v_a_3712_);
                        if v___x_3713_ == 0 {
                            v_a_3703_ = v_b_3698_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v___x_3708_);
                            v___x_3714_ = l_Lean_Expr_isTrue(v___x_3708_);
                            if v___x_3714_ == 0 {
                                lean_inc(v___x_3708_);
                                v___x_3715_ = l_Lean_Expr_isFalse(v___x_3708_);
                                if v___x_3715_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    v_a_3703_ = v_b_3698_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_3703_ = v_b_3698_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        if lean_obj_tag(v___x_3711_) == 0 {
                            v_a_3716_ = lean_ctor_get(v___x_3711_, 0);
                            lean_inc(v_a_3716_);
                            lean_dec_ref_known(v___x_3711_, 1);
                            v___x_3717_ = (lean_unbox(v_a_3716_) as u8);
                            lean_dec(v_a_3716_);
                            if v___x_3717_ == 0 {
                                v_a_3703_ = v_b_3698_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_b_3698_);
                            lean_dec(v_filter_3694_);
                            v_a_3718_ = lean_ctor_get(v___x_3711_, 0);
                            v_isSharedCheck_3725_ = (!lean_is_exclusive(v___x_3711_)) as u8;
                            if v_isSharedCheck_3725_ == 0 {
                                v___x_3720_ = v___x_3711_;
                                v_isShared_3721_ = v_isSharedCheck_3725_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3718_);
                                lean_dec(v___x_3711_);
                                v___x_3720_ = lean_box(0);
                                v_isShared_3721_ = v_isSharedCheck_3725_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_filter_3694_);
                    v___x_3726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3726_, 0, v_b_3698_);
                    return v___x_3726_;
                }
            }
            1 => {
                v___x_3704_ = 1usize;
                v___x_3705_ = lean_usize_add(v_i_3696_, v___x_3704_);
                v_i_3696_ = v___x_3705_;
                v_b_3698_ = v_a_3703_;
                state = 0;
                continue;
            }
            2 => {
                lean_inc(v___x_3708_);
                v___x_3710_ = lean_array_push(v_b_3698_, v___x_3708_);
                v_a_3703_ = v___x_3710_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_3721_ == 0 {
                    v___x_3723_ = v___x_3720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
                    v___x_3723_ = v_reuseFailAlloc_3724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg___boxed(
    mut v_filter_3727_: *mut LeanObject,
    mut v_as_3728_: *mut LeanObject,
    mut v_i_3729_: *mut LeanObject,
    mut v_stop_3730_: *mut LeanObject,
    mut v_b_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3735_: usize = 0;
    let mut v_stop_boxed_3736_: usize = 0;
    let mut v_res_3737_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3735_ = lean_unbox_usize(v_i_3729_);
    lean_dec(v_i_3729_);
    v_stop_boxed_3736_ = lean_unbox_usize(v_stop_3730_);
    lean_dec(v_stop_3730_);
    v_res_3737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_3727_, v_as_3728_, v_i_boxed_3735_, v_stop_boxed_3736_, v_b_3731_, v___y_3732_, v___y_3733_);
    lean_dec(v___y_3733_);
    lean_dec(v___y_3732_);
    lean_dec_ref(v_as_3728_);
    return v_res_3737_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(
    mut v_filter_3738_: *mut LeanObject,
    mut v_isTrue_3739_: u8,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
    mut v___y_3748_: *mut LeanObject,
    mut v___y_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: usize = 0;
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: usize = 0;
    let mut v___x_3776_: usize = 0;
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3778_: u8 = 0;
    let mut v_a_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3786_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_isTrue_3739_ == 0 {
                    v___x_3787_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v___y_3744_);
                    v___y_3752_ = v___x_3787_;
                    state = 1;
                    continue;
                } else {
                    v___x_3788_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v___y_3744_);
                    v___y_3752_ = v___x_3788_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_3752_) == 0 {
                    v_a_3753_ = lean_ctor_get(v___y_3752_, 0);
                    v_isSharedCheck_3778_ = (!lean_is_exclusive(v___y_3752_)) as u8;
                    if v_isSharedCheck_3778_ == 0 {
                        v___x_3755_ = v___y_3752_;
                        v_isShared_3756_ = v_isSharedCheck_3778_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3753_);
                        lean_dec(v___y_3752_);
                        v___x_3755_ = lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3778_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_filter_3738_);
                    v_a_3779_ = lean_ctor_get(v___y_3752_, 0);
                    v_isSharedCheck_3786_ = (!lean_is_exclusive(v___y_3752_)) as u8;
                    if v_isSharedCheck_3786_ == 0 {
                        v___x_3781_ = v___y_3752_;
                        v_isShared_3782_ = v_isSharedCheck_3786_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3779_);
                        lean_dec(v___y_3752_);
                        v___x_3781_ = lean_box(0);
                        v_isShared_3782_ = v_isSharedCheck_3786_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3757_ = lean_st_ref_get(v___y_3740_);
                v___x_3758_ = 0;
                v___x_3759_ = l_Lean_Meta_Grind_Goal_getEqc(v___x_3757_, v_a_3753_, v___x_3758_);
                lean_dec(v___x_3757_);
                v___x_3760_ = lean_array_mk(v___x_3759_);
                v___x_3761_ = lean_unsigned_to_nat(0);
                v___x_3762_ = lean_array_get_size(v___x_3760_);
                v___x_3763_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___lam__0___closed__0;
                v___x_3764_ = lean_nat_dec_lt(v___x_3761_, v___x_3762_);
                if v___x_3764_ == 0 {
                    lean_dec_ref(v___x_3760_);
                    lean_dec(v_filter_3738_);
                    if v_isShared_3756_ == 0 {
                        lean_ctor_set(v___x_3755_, 0, v___x_3763_);
                        v___x_3766_ = v___x_3755_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3763_);
                        v___x_3766_ = v_reuseFailAlloc_3767_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3768_ = lean_nat_dec_le(v___x_3762_, v___x_3762_);
                    if v___x_3768_ == 0 {
                        if v___x_3764_ == 0 {
                            lean_dec_ref(v___x_3760_);
                            lean_dec(v_filter_3738_);
                            if v_isShared_3756_ == 0 {
                                lean_ctor_set(v___x_3755_, 0, v___x_3763_);
                                v___x_3770_ = v___x_3755_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3763_);
                                v___x_3770_ = v_reuseFailAlloc_3771_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3755_);
                            v___x_3772_ = 0usize;
                            v___x_3773_ = lean_usize_of_nat(v___x_3762_);
                            v___x_3774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_3738_, v___x_3760_, v___x_3772_, v___x_3773_, v___x_3763_, v___y_3740_, v___y_3747_);
                            lean_dec_ref(v___x_3760_);
                            return v___x_3774_;
                        }
                    } else {
                        lean_del_object(v___x_3755_);
                        v___x_3775_ = 0usize;
                        v___x_3776_ = lean_usize_of_nat(v___x_3762_);
                        v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_3738_, v___x_3760_, v___x_3775_, v___x_3776_, v___x_3763_, v___y_3740_, v___y_3747_);
                        lean_dec_ref(v___x_3760_);
                        return v___x_3777_;
                    }
                }
            }
            3 => {
                return v___x_3766_;
            }
            4 => {
                return v___x_3770_;
            }
            5 => {
                if v_isShared_3782_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
                    v___x_3784_ = v_reuseFailAlloc_3785_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed(
    mut v_filter_3789_: *mut LeanObject,
    mut v_isTrue_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isTrue_boxed_3802_: u8 = 0;
    let mut v_res_3803_: *mut LeanObject = core::ptr::null_mut();
    v_isTrue_boxed_3802_ = (lean_unbox(v_isTrue_3790_) as u8);
    v_res_3803_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0(v_filter_3789_, v_isTrue_boxed_3802_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
    lean_dec(v___y_3800_);
    lean_dec_ref(v___y_3799_);
    lean_dec(v___y_3798_);
    lean_dec_ref(v___y_3797_);
    lean_dec(v___y_3796_);
    lean_dec_ref(v___y_3795_);
    lean_dec(v___y_3794_);
    lean_dec_ref(v___y_3793_);
    lean_dec(v___y_3792_);
    lean_dec(v___y_3791_);
    return v_res_3803_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(
    mut v_filter_3810_: *mut LeanObject,
    mut v_isTrue_3811_: u8,
    mut v_collapsed_3812_: u8,
    mut v_a_3813_: *mut LeanObject,
    mut v_a_3814_: *mut LeanObject,
    mut v_a_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3847_: u8 = 0;
    let mut v_a_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3820_ = lean_box((v_isTrue_3811_) as usize);
                v___f_3821_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                lean_closure_set(v___f_3821_, 0, v_filter_3810_);
                lean_closure_set(v___f_3821_, 1, v___x_3820_);
                v___x_3822_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(
                    v___f_3821_,
                    v_a_3813_,
                    v_a_3814_,
                    v_a_3815_,
                    v_a_3816_,
                    v_a_3817_,
                    v_a_3818_,
                );
                if lean_obj_tag(v___x_3822_) == 0 {
                    v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
                    v_isSharedCheck_3847_ = (!lean_is_exclusive(v___x_3822_)) as u8;
                    if v_isSharedCheck_3847_ == 0 {
                        v___x_3825_ = v___x_3822_;
                        v_isShared_3826_ = v_isSharedCheck_3847_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3823_);
                        lean_dec(v___x_3822_);
                        v___x_3825_ = lean_box(0);
                        v_isShared_3826_ = v_isSharedCheck_3847_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3848_ = lean_ctor_get(v___x_3822_, 0);
                    v_isSharedCheck_3855_ = (!lean_is_exclusive(v___x_3822_)) as u8;
                    if v_isSharedCheck_3855_ == 0 {
                        v___x_3850_ = v___x_3822_;
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3848_);
                        lean_dec(v___x_3822_);
                        v___x_3850_ = lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3827_ = lean_array_get_size(v_a_3823_);
                v___x_3828_ = lean_unsigned_to_nat(0);
                v___x_3829_ = lean_nat_dec_eq(v___x_3827_, v___x_3828_);
                if v___x_3829_ == 0 {
                    v___x_3830_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__1;
                    if v_isTrue_3811_ == 0 {
                        v___x_3841_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__3;
                        v___y_3832_ = v___x_3841_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3842_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__4;
                        v___y_3832_ = v___x_3842_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3823_);
                    v___x_3843_ = lean_box(0);
                    if v_isShared_3826_ == 0 {
                        lean_ctor_set(v___x_3825_, 0, v___x_3843_);
                        v___x_3845_ = v___x_3825_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3846_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3846_, 0, v___x_3843_);
                        v___x_3845_ = v_reuseFailAlloc_3846_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3833_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2;
                lean_inc_ref(v___y_3832_);
                v___x_3834_ = lean_string_append(v___y_3832_, v___x_3833_);
                v___x_3835_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg___closed__4;
                v___x_3836_ = l_Lean_Meta_Grind_ppExprArray(
                    v___x_3830_,
                    v___x_3834_,
                    v_a_3823_,
                    v___x_3835_,
                    v_collapsed_3812_,
                );
                v___x_3837_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v___x_3836_);
                if v_isShared_3826_ == 0 {
                    lean_ctor_set(v___x_3825_, 0, v___x_3837_);
                    v___x_3839_ = v___x_3825_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
                    v___x_3839_ = v_reuseFailAlloc_3840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3839_;
            }
            4 => {
                return v___x_3845_;
            }
            5 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
                    v___x_3853_ = v_reuseFailAlloc_3854_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___boxed(
    mut v_filter_3856_: *mut LeanObject,
    mut v_isTrue_3857_: *mut LeanObject,
    mut v_collapsed_3858_: *mut LeanObject,
    mut v_a_3859_: *mut LeanObject,
    mut v_a_3860_: *mut LeanObject,
    mut v_a_3861_: *mut LeanObject,
    mut v_a_3862_: *mut LeanObject,
    mut v_a_3863_: *mut LeanObject,
    mut v_a_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isTrue_boxed_3866_: u8 = 0;
    let mut v_collapsed_boxed_3867_: u8 = 0;
    let mut v_res_3868_: *mut LeanObject = core::ptr::null_mut();
    v_isTrue_boxed_3866_ = (lean_unbox(v_isTrue_3857_) as u8);
    v_collapsed_boxed_3867_ = (lean_unbox(v_collapsed_3858_) as u8);
    v_res_3868_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(
            v_filter_3856_,
            v_isTrue_boxed_3866_,
            v_collapsed_boxed_3867_,
            v_a_3859_,
            v_a_3860_,
            v_a_3861_,
            v_a_3862_,
            v_a_3863_,
            v_a_3864_,
        );
    lean_dec(v_a_3864_);
    lean_dec_ref(v_a_3863_);
    lean_dec(v_a_3862_);
    lean_dec_ref(v_a_3861_);
    lean_dec(v_a_3860_);
    lean_dec_ref(v_a_3859_);
    return v_res_3868_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(
    mut v_filter_3869_: *mut LeanObject,
    mut v_isTrue_3870_: u8,
    mut v_collapsed_3871_: u8,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
    mut v_a_3877_: *mut LeanObject,
    mut v_a_3878_: *mut LeanObject,
    mut v_a_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    v___x_3881_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(
            v_filter_3869_,
            v_isTrue_3870_,
            v_collapsed_3871_,
            v_a_3872_,
            v_a_3873_,
            v_a_3876_,
            v_a_3877_,
            v_a_3878_,
            v_a_3879_,
        );
    return v___x_3881_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___boxed(
    mut v_filter_3882_: *mut LeanObject,
    mut v_isTrue_3883_: *mut LeanObject,
    mut v_collapsed_3884_: *mut LeanObject,
    mut v_a_3885_: *mut LeanObject,
    mut v_a_3886_: *mut LeanObject,
    mut v_a_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
    mut v_a_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isTrue_boxed_3894_: u8 = 0;
    let mut v_collapsed_boxed_3895_: u8 = 0;
    let mut v_res_3896_: *mut LeanObject = core::ptr::null_mut();
    v_isTrue_boxed_3894_ = (lean_unbox(v_isTrue_3883_) as u8);
    v_collapsed_boxed_3895_ = (lean_unbox(v_collapsed_3884_) as u8);
    v_res_3896_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f(
            v_filter_3882_,
            v_isTrue_boxed_3894_,
            v_collapsed_boxed_3895_,
            v_a_3885_,
            v_a_3886_,
            v_a_3887_,
            v_a_3888_,
            v_a_3889_,
            v_a_3890_,
            v_a_3891_,
            v_a_3892_,
        );
    lean_dec(v_a_3892_);
    lean_dec_ref(v_a_3891_);
    lean_dec(v_a_3890_);
    lean_dec_ref(v_a_3889_);
    lean_dec(v_a_3888_);
    lean_dec_ref(v_a_3887_);
    lean_dec(v_a_3886_);
    lean_dec_ref(v_a_3885_);
    return v_res_3896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(
    mut v_filter_3897_: *mut LeanObject,
    mut v_as_3898_: *mut LeanObject,
    mut v_i_3899_: usize,
    mut v_stop_3900_: usize,
    mut v_b_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    v___x_3913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___redArg(v_filter_3897_, v_as_3898_, v_i_3899_, v_stop_3900_, v_b_3901_, v___y_3902_, v___y_3909_);
    return v___x_3913_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0___boxed(
    mut v_filter_3914_: *mut LeanObject,
    mut v_as_3915_: *mut LeanObject,
    mut v_i_3916_: *mut LeanObject,
    mut v_stop_3917_: *mut LeanObject,
    mut v_b_3918_: *mut LeanObject,
    mut v___y_3919_: *mut LeanObject,
    mut v___y_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
    mut v___y_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3930_: usize = 0;
    let mut v_stop_boxed_3931_: usize = 0;
    let mut v_res_3932_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3930_ = lean_unbox_usize(v_i_3916_);
    lean_dec(v_i_3916_);
    v_stop_boxed_3931_ = lean_unbox_usize(v_stop_3917_);
    lean_dec(v_stop_3917_);
    v_res_3932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f_spec__0(v_filter_3914_, v_as_3915_, v_i_boxed_3930_, v_stop_boxed_3931_, v_b_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
    lean_dec(v___y_3928_);
    lean_dec_ref(v___y_3927_);
    lean_dec(v___y_3926_);
    lean_dec_ref(v___y_3925_);
    lean_dec(v___y_3924_);
    lean_dec_ref(v___y_3923_);
    lean_dec(v___y_3922_);
    lean_dec_ref(v___y_3921_);
    lean_dec(v___y_3920_);
    lean_dec(v___y_3919_);
    lean_dec_ref(v_as_3915_);
    return v_res_3932_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(
    mut v_filter_x3f_3936_: *mut LeanObject,
    mut v_isTrue_3937_: u8,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
    mut v___y_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3947_ = l_Lean_Elab_Tactic_Grind_elabFilter(
                    v_filter_x3f_3936_,
                    v___y_3938_,
                    v___y_3939_,
                    v___y_3940_,
                    v___y_3941_,
                    v___y_3942_,
                    v___y_3943_,
                    v___y_3944_,
                    v___y_3945_,
                );
                if lean_obj_tag(v___x_3947_) == 0 {
                    v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
                    lean_inc(v_a_3948_);
                    lean_dec_ref_known(v___x_3947_, 1);
                    v___x_3949_ = 0;
                    v___x_3950_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_a_3948_, v_isTrue_3937_, v___x_3949_, v___y_3938_, v___y_3939_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
                    if lean_obj_tag(v___x_3950_) == 0 {
                        v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
                        lean_inc(v_a_3951_);
                        lean_dec_ref_known(v___x_3950_, 1);
                        if lean_obj_tag(v_a_3951_) == 1 {
                            v_val_3952_ = lean_ctor_get(v_a_3951_, 0);
                            lean_inc(v_val_3952_);
                            lean_dec_ref_known(v_a_3951_, 1);
                            v___x_3953_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_3952_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
                            return v___x_3953_;
                        } else {
                            lean_dec(v_a_3951_);
                            v___x_3954_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__0;
                            if v_isTrue_3937_ == 0 {
                                v___x_3963_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__1;
                                v___y_3956_ = v___x_3963_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3964_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___closed__2;
                                v___y_3956_ = v___x_3964_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_3965_ = lean_ctor_get(v___x_3950_, 0);
                        v_isSharedCheck_3972_ = (!lean_is_exclusive(v___x_3950_)) as u8;
                        if v_isSharedCheck_3972_ == 0 {
                            v___x_3967_ = v___x_3950_;
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3965_);
                            lean_dec(v___x_3950_);
                            v___x_3967_ = lean_box(0);
                            v_isShared_3968_ = v_isSharedCheck_3972_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_3973_ = lean_ctor_get(v___x_3947_, 0);
                    v_isSharedCheck_3980_ = (!lean_is_exclusive(v___x_3947_)) as u8;
                    if v_isSharedCheck_3980_ == 0 {
                        v___x_3975_ = v___x_3947_;
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3973_);
                        lean_dec(v___x_3947_);
                        v___x_3975_ = lean_box(0);
                        v_isShared_3976_ = v_isSharedCheck_3980_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3957_ = lean_string_append(v___x_3954_, v___y_3956_);
                v___x_3958_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg___closed__2;
                v___x_3959_ = lean_string_append(v___x_3957_, v___x_3958_);
                v___x_3960_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3960_, 0, v___x_3959_);
                v___x_3961_ = l_Lean_MessageData_ofFormat(v___x_3960_);
                v___x_3962_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_3961_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
                return v___x_3962_;
            }
            2 => {
                if v_isShared_3968_ == 0 {
                    v___x_3970_ = v___x_3967_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3970_;
            }
            4 => {
                if v_isShared_3976_ == 0 {
                    v___x_3978_ = v___x_3975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
                    v___x_3978_ = v_reuseFailAlloc_3979_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed(
    mut v_filter_x3f_3981_: *mut LeanObject,
    mut v_isTrue_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isTrue_boxed_3992_: u8 = 0;
    let mut v_res_3993_: *mut LeanObject = core::ptr::null_mut();
    v_isTrue_boxed_3992_ = (lean_unbox(v_isTrue_3982_) as u8);
    v_res_3993_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0(
            v_filter_x3f_3981_,
            v_isTrue_boxed_3992_,
            v___y_3983_,
            v___y_3984_,
            v___y_3985_,
            v___y_3986_,
            v___y_3987_,
            v___y_3988_,
            v___y_3989_,
            v___y_3990_,
        );
    lean_dec(v___y_3990_);
    lean_dec_ref(v___y_3989_);
    lean_dec(v___y_3988_);
    lean_dec_ref(v___y_3987_);
    lean_dec(v___y_3986_);
    lean_dec_ref(v___y_3985_);
    lean_dec(v___y_3984_);
    lean_dec_ref(v___y_3983_);
    return v_res_3993_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(
    mut v_filter_x3f_3994_: *mut LeanObject,
    mut v_isTrue_3995_: u8,
    mut v_a_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    v___x_4005_ = lean_box((v_isTrue_3995_) as usize);
    v___f_4006_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___lam__0___boxed as *mut core::ffi::c_void, 11, 2);
    lean_closure_set(v___f_4006_, 0, v_filter_x3f_3994_);
    lean_closure_set(v___f_4006_, 1, v___x_4005_);
    v___x_4007_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___f_4006_,
        v_a_3996_,
        v_a_3997_,
        v_a_3998_,
        v_a_3999_,
        v_a_4000_,
        v_a_4001_,
        v_a_4002_,
        v_a_4003_,
    );
    return v___x_4007_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps___boxed(
    mut v_filter_x3f_4008_: *mut LeanObject,
    mut v_isTrue_4009_: *mut LeanObject,
    mut v_a_4010_: *mut LeanObject,
    mut v_a_4011_: *mut LeanObject,
    mut v_a_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
    mut v_a_4014_: *mut LeanObject,
    mut v_a_4015_: *mut LeanObject,
    mut v_a_4016_: *mut LeanObject,
    mut v_a_4017_: *mut LeanObject,
    mut v_a_4018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isTrue_boxed_4019_: u8 = 0;
    let mut v_res_4020_: *mut LeanObject = core::ptr::null_mut();
    v_isTrue_boxed_4019_ = (lean_unbox(v_isTrue_4009_) as u8);
    v_res_4020_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(
        v_filter_x3f_4008_,
        v_isTrue_boxed_4019_,
        v_a_4010_,
        v_a_4011_,
        v_a_4012_,
        v_a_4013_,
        v_a_4014_,
        v_a_4015_,
        v_a_4016_,
        v_a_4017_,
    );
    lean_dec(v_a_4017_);
    lean_dec_ref(v_a_4016_);
    lean_dec(v_a_4015_);
    lean_dec_ref(v_a_4014_);
    lean_dec(v_a_4013_);
    lean_dec_ref(v_a_4012_);
    lean_dec(v_a_4011_);
    lean_dec_ref(v_a_4010_);
    return v_res_4020_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(
    mut v_stx_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
    mut v_a_4036_: *mut LeanObject,
    mut v_a_4037_: *mut LeanObject,
    mut v_a_4038_: *mut LeanObject,
    mut v_a_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: u8 = 0;
    v___x_4044_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1;
    lean_inc(v_stx_4034_);
    v___x_4045_ = l_Lean_Syntax_isOfKind(v_stx_4034_, v___x_4044_);
    if v___x_4045_ == 0 {
        let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_4034_);
        v___x_4046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
        return v___x_4046_;
    } else {
        let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4050_: u8 = 0;
        v___x_4047_ = lean_unsigned_to_nat(1);
        v___x_4048_ = l_Lean_Syntax_getArg(v_stx_4034_, v___x_4047_);
        lean_dec(v_stx_4034_);
        v___x_4049_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2;
        lean_inc(v___x_4048_);
        v___x_4050_ = l_Lean_Syntax_isOfKind(v___x_4048_, v___x_4049_);
        if v___x_4050_ == 0 {
            let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_4048_);
            v___x_4051_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
            return v___x_4051_;
        } else {
            let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4054_: u8 = 0;
            v___x_4052_ = lean_unsigned_to_nat(0);
            v___x_4053_ = l_Lean_Syntax_getArg(v___x_4048_, v___x_4052_);
            lean_dec(v___x_4048_);
            v___x_4054_ = l_Lean_Syntax_isNone(v___x_4053_);
            if v___x_4054_ == 0 {
                let mut v___x_4055_: u8 = 0;
                lean_inc(v___x_4053_);
                v___x_4055_ = l_Lean_Syntax_matchesNull(v___x_4053_, v___x_4047_);
                if v___x_4055_ == 0 {
                    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_4053_);
                    v___x_4056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_4056_;
                } else {
                    let mut v_filter_x3f_4057_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
                    v_filter_x3f_4057_ = l_Lean_Syntax_getArg(v___x_4053_, v___x_4052_);
                    lean_dec(v___x_4053_);
                    v___x_4058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4058_, 0, v_filter_x3f_4057_);
                    v___x_4059_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v___x_4058_, v___x_4050_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
                    return v___x_4059_;
                }
            } else {
                let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_4053_);
                v___x_4060_ = lean_box(0);
                v___x_4061_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v___x_4060_, v___x_4050_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
                return v___x_4061_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed(
    mut v_stx_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4072_: *mut LeanObject = core::ptr::null_mut();
    v_res_4072_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue(
            v_stx_4062_,
            v_a_4063_,
            v_a_4064_,
            v_a_4065_,
            v_a_4066_,
            v_a_4067_,
            v_a_4068_,
            v_a_4069_,
            v_a_4070_,
        );
    lean_dec(v_a_4070_);
    lean_dec_ref(v_a_4069_);
    lean_dec(v_a_4068_);
    lean_dec_ref(v_a_4067_);
    lean_dec(v_a_4066_);
    lean_dec_ref(v_a_4065_);
    lean_dec(v_a_4064_);
    lean_dec_ref(v_a_4063_);
    return v_res_4072_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1()
-> *mut LeanObject {
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    v___x_4078_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_4079_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__1;
    v___x_4080_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___closed__1;
    v___x_4081_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4082_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4078_,
        v___x_4079_,
        v___x_4080_,
        v___x_4081_,
    );
    return v___x_4082_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1___boxed(
    mut v_a_4083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4084_: *mut LeanObject = core::ptr::null_mut();
    v_res_4084_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
    return v_res_4084_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(
    mut v_stx_4092_: *mut LeanObject,
    mut v_a_4093_: *mut LeanObject,
    mut v_a_4094_: *mut LeanObject,
    mut v_a_4095_: *mut LeanObject,
    mut v_a_4096_: *mut LeanObject,
    mut v_a_4097_: *mut LeanObject,
    mut v_a_4098_: *mut LeanObject,
    mut v_a_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_x3f_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: u8 = 0;
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4114_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1;
                lean_inc(v_stx_4092_);
                v___x_4115_ = l_Lean_Syntax_isOfKind(v_stx_4092_, v___x_4114_);
                if v___x_4115_ == 0 {
                    lean_dec(v_stx_4092_);
                    v___x_4116_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_4116_;
                } else {
                    v___x_4117_ = lean_unsigned_to_nat(1);
                    v___x_4118_ = l_Lean_Syntax_getArg(v_stx_4092_, v___x_4117_);
                    lean_dec(v_stx_4092_);
                    v___x_4119_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___closed__2;
                    lean_inc(v___x_4118_);
                    v___x_4120_ = l_Lean_Syntax_isOfKind(v___x_4118_, v___x_4119_);
                    if v___x_4120_ == 0 {
                        lean_dec(v___x_4118_);
                        v___x_4121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_4121_;
                    } else {
                        v___x_4122_ = lean_unsigned_to_nat(0);
                        v___x_4123_ = l_Lean_Syntax_getArg(v___x_4118_, v___x_4122_);
                        lean_dec(v___x_4118_);
                        v___x_4124_ = l_Lean_Syntax_isNone(v___x_4123_);
                        if v___x_4124_ == 0 {
                            lean_inc(v___x_4123_);
                            v___x_4125_ = l_Lean_Syntax_matchesNull(v___x_4123_, v___x_4117_);
                            if v___x_4125_ == 0 {
                                lean_dec(v___x_4123_);
                                v___x_4126_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                                return v___x_4126_;
                            } else {
                                v_filter_x3f_4127_ = l_Lean_Syntax_getArg(v___x_4123_, v___x_4122_);
                                lean_dec(v___x_4123_);
                                v___x_4128_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4128_, 0, v_filter_x3f_4127_);
                                v_filter_x3f_4103_ = v___x_4128_;
                                v___y_4104_ = v_a_4093_;
                                v___y_4105_ = v_a_4094_;
                                v___y_4106_ = v_a_4095_;
                                v___y_4107_ = v_a_4096_;
                                v___y_4108_ = v_a_4097_;
                                v___y_4109_ = v_a_4098_;
                                v___y_4110_ = v_a_4099_;
                                v___y_4111_ = v_a_4100_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4123_);
                            v___x_4129_ = lean_box(0);
                            v_filter_x3f_4103_ = v___x_4129_;
                            v___y_4104_ = v_a_4093_;
                            v___y_4105_ = v_a_4094_;
                            v___y_4106_ = v_a_4095_;
                            v___y_4107_ = v_a_4096_;
                            v___y_4108_ = v_a_4097_;
                            v___y_4109_ = v_a_4098_;
                            v___y_4110_ = v_a_4099_;
                            v___y_4111_ = v_a_4100_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4112_ = 0;
                v___x_4113_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_showProps(v_filter_x3f_4103_, v___x_4112_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
                return v___x_4113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed(
    mut v_stx_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
    mut v_a_4134_: *mut LeanObject,
    mut v_a_4135_: *mut LeanObject,
    mut v_a_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
    mut v_a_4138_: *mut LeanObject,
    mut v_a_4139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4140_: *mut LeanObject = core::ptr::null_mut();
    v_res_4140_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse(
            v_stx_4130_,
            v_a_4131_,
            v_a_4132_,
            v_a_4133_,
            v_a_4134_,
            v_a_4135_,
            v_a_4136_,
            v_a_4137_,
            v_a_4138_,
        );
    lean_dec(v_a_4138_);
    lean_dec_ref(v_a_4137_);
    lean_dec(v_a_4136_);
    lean_dec_ref(v_a_4135_);
    lean_dec(v_a_4134_);
    lean_dec_ref(v_a_4133_);
    lean_dec(v_a_4132_);
    lean_dec_ref(v_a_4131_);
    return v_res_4140_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1()
-> *mut LeanObject {
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_4146_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_4147_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___closed__1;
    v___x_4148_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___closed__1;
    v___x_4149_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4150_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4146_,
        v___x_4147_,
        v___x_4148_,
        v___x_4149_,
    );
    return v___x_4150_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1___boxed(
    mut v_a_4151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4152_: *mut LeanObject = core::ptr::null_mut();
    v_res_4152_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
    return v_res_4152_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(
    mut v_filter_4153_: *mut LeanObject,
    mut v_x_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4154_) == 0 {
                    lean_dec(v_filter_4153_);
                    v___x_4158_ = 0;
                    v___x_4159_ = lean_box((v___x_4158_) as usize);
                    v___x_4160_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4160_, 0, v___x_4159_);
                    return v___x_4160_;
                } else {
                    v_head_4161_ = lean_ctor_get(v_x_4154_, 0);
                    lean_inc(v_head_4161_);
                    v_tail_4162_ = lean_ctor_get(v_x_4154_, 1);
                    lean_inc(v_tail_4162_);
                    lean_dec_ref_known(v_x_4154_, 2);
                    lean_inc(v_filter_4153_);
                    v___x_4163_ = l___private_Lean_Meta_Tactic_Grind_Filter_0__Lean_Meta_Grind_Filter_eval_go___redArg(v_head_4161_, v_filter_4153_, v___y_4155_, v___y_4156_);
                    if lean_obj_tag(v___x_4163_) == 0 {
                        v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
                        lean_inc(v_a_4164_);
                        v___x_4165_ = (lean_unbox(v_a_4164_) as u8);
                        lean_dec(v_a_4164_);
                        if v___x_4165_ == 0 {
                            lean_dec_ref_known(v___x_4163_, 1);
                            v_x_4154_ = v_tail_4162_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_tail_4162_);
                            lean_dec(v_filter_4153_);
                            return v___x_4163_;
                        }
                    } else {
                        lean_dec(v_tail_4162_);
                        lean_dec(v_filter_4153_);
                        return v___x_4163_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg___boxed(
    mut v_filter_4167_: *mut LeanObject,
    mut v_x_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
    mut v___y_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4172_: *mut LeanObject = core::ptr::null_mut();
    v_res_4172_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_4167_, v_x_4168_, v___y_4169_, v___y_4170_);
    lean_dec(v___y_4170_);
    lean_dec(v___y_4169_);
    return v_res_4172_;
}
pub unsafe fn l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(
    mut v_x_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4173_) == 0 {
                    v___x_4174_ = lean_box(0);
                    return v___x_4174_;
                } else {
                    v_head_4175_ = lean_ctor_get(v_x_4173_, 0);
                    lean_inc_n(v_head_4175_, 2);
                    v_tail_4176_ = lean_ctor_get(v_x_4173_, 1);
                    lean_inc(v_tail_4176_);
                    lean_dec_ref_known(v_x_4173_, 2);
                    v___x_4177_ = l_Lean_Expr_isFalse(v_head_4175_);
                    if v___x_4177_ == 0 {
                        lean_dec(v_head_4175_);
                        v_x_4173_ = v_tail_4176_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_4176_);
                        v___x_4179_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4179_, 0, v_head_4175_);
                        return v___x_4179_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(
    mut v_x_4180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: u8 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4180_) == 0 {
                    v___x_4181_ = lean_box(0);
                    return v___x_4181_;
                } else {
                    v_head_4182_ = lean_ctor_get(v_x_4180_, 0);
                    lean_inc_n(v_head_4182_, 2);
                    v_tail_4183_ = lean_ctor_get(v_x_4180_, 1);
                    lean_inc(v_tail_4183_);
                    lean_dec_ref_known(v_x_4180_, 2);
                    v___x_4184_ = l_Lean_Expr_isTrue(v_head_4182_);
                    if v___x_4184_ == 0 {
                        lean_dec(v_head_4182_);
                        v_x_4180_ = v_tail_4183_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_4183_);
                        v___x_4186_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4186_, 0, v_head_4182_);
                        return v___x_4186_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(
    mut v_x_4187_: *mut LeanObject,
    mut v_x_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: u8 = 0;
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4215_: u8 = 0;
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4187_) == 0 {
                    v___x_4194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4194_, 0, v_x_4188_);
                    return v___x_4194_;
                } else {
                    v_head_4195_ = lean_ctor_get(v_x_4187_, 0);
                    v_tail_4196_ = lean_ctor_get(v_x_4187_, 1);
                    v_isSharedCheck_4216_ = (!lean_is_exclusive(v_x_4187_)) as u8;
                    if v_isSharedCheck_4216_ == 0 {
                        v___x_4198_ = v_x_4187_;
                        v_isShared_4199_ = v_isSharedCheck_4216_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4196_);
                        lean_inc(v_head_4195_);
                        lean_dec(v_x_4187_);
                        v___x_4198_ = lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4216_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4195_);
                v___x_4200_ = l_Lean_Meta_Grind_isSupportApp(
                    v_head_4195_,
                    v___y_4189_,
                    v___y_4190_,
                    v___y_4191_,
                    v___y_4192_,
                );
                if lean_obj_tag(v___x_4200_) == 0 {
                    v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
                    lean_inc(v_a_4201_);
                    lean_dec_ref_known(v___x_4200_, 1);
                    v___x_4202_ = (lean_unbox(v_a_4201_) as u8);
                    lean_dec(v_a_4201_);
                    if v___x_4202_ == 0 {
                        lean_del_object(v___x_4198_);
                        lean_dec(v_head_4195_);
                        v_x_4187_ = v_tail_4196_;
                        state = 0;
                        continue;
                    } else {
                        if v_isShared_4199_ == 0 {
                            lean_ctor_set(v___x_4198_, 1, v_x_4188_);
                            v___x_4205_ = v___x_4198_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_head_4195_);
                            lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_x_4188_);
                            v___x_4205_ = v_reuseFailAlloc_4207_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4198_);
                    lean_dec(v_tail_4196_);
                    lean_dec(v_head_4195_);
                    lean_dec(v_x_4188_);
                    v_a_4208_ = lean_ctor_get(v___x_4200_, 0);
                    v_isSharedCheck_4215_ = (!lean_is_exclusive(v___x_4200_)) as u8;
                    if v_isSharedCheck_4215_ == 0 {
                        v___x_4210_ = v___x_4200_;
                        v_isShared_4211_ = v_isSharedCheck_4215_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4208_);
                        lean_dec(v___x_4200_);
                        v___x_4210_ = lean_box(0);
                        v_isShared_4211_ = v_isSharedCheck_4215_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4187_ = v_tail_4196_;
                v_x_4188_ = v___x_4205_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4211_ == 0 {
                    v___x_4213_ = v___x_4210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
                    v___x_4213_ = v_reuseFailAlloc_4214_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg___boxed(
    mut v_x_4217_: *mut LeanObject,
    mut v_x_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4224_: *mut LeanObject = core::ptr::null_mut();
    v_res_4224_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_x_4217_, v_x_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
    lean_dec(v___y_4222_);
    lean_dec_ref(v___y_4221_);
    lean_dec(v___y_4220_);
    lean_dec_ref(v___y_4219_);
    return v_res_4224_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(
    mut v_a_4225_: u8,
    mut v_a_4226_: u8,
    mut v_x_4227_: *mut LeanObject,
    mut v_x_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4239_: u8 = 0;
    let mut v_a_4241_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v_a_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: u8 = 0;
    let mut v_a_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4227_) == 0 {
                    v___x_4234_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4234_, 0, v_x_4228_);
                    return v___x_4234_;
                } else {
                    v_head_4235_ = lean_ctor_get(v_x_4227_, 0);
                    v_tail_4236_ = lean_ctor_get(v_x_4227_, 1);
                    v_isSharedCheck_4260_ = (!lean_is_exclusive(v_x_4227_)) as u8;
                    if v_isSharedCheck_4260_ == 0 {
                        v___x_4238_ = v_x_4227_;
                        v_isShared_4239_ = v_isSharedCheck_4260_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4236_);
                        lean_inc(v_head_4235_);
                        lean_dec(v_x_4227_);
                        v___x_4238_ = lean_box(0);
                        v_isShared_4239_ = v_isSharedCheck_4260_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4235_);
                v___x_4247_ = l_Lean_Meta_Grind_isSupportApp(
                    v_head_4235_,
                    v___y_4229_,
                    v___y_4230_,
                    v___y_4231_,
                    v___y_4232_,
                );
                if lean_obj_tag(v___x_4247_) == 0 {
                    v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
                    lean_inc(v_a_4248_);
                    lean_dec_ref_known(v___x_4247_, 1);
                    v___x_4249_ = (lean_unbox(v_a_4248_) as u8);
                    lean_dec(v_a_4248_);
                    if v___x_4249_ == 0 {
                        v_a_4241_ = v_a_4225_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4241_ = v_a_4226_;
                        state = 2;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_4247_) == 0 {
                        v_a_4250_ = lean_ctor_get(v___x_4247_, 0);
                        lean_inc(v_a_4250_);
                        lean_dec_ref_known(v___x_4247_, 1);
                        v___x_4251_ = (lean_unbox(v_a_4250_) as u8);
                        lean_dec(v_a_4250_);
                        v_a_4241_ = v___x_4251_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_4238_);
                        lean_dec(v_tail_4236_);
                        lean_dec(v_head_4235_);
                        lean_dec(v_x_4228_);
                        v_a_4252_ = lean_ctor_get(v___x_4247_, 0);
                        v_isSharedCheck_4259_ = (!lean_is_exclusive(v___x_4247_)) as u8;
                        if v_isSharedCheck_4259_ == 0 {
                            v___x_4254_ = v___x_4247_;
                            v_isShared_4255_ = v_isSharedCheck_4259_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4252_);
                            lean_dec(v___x_4247_);
                            v___x_4254_ = lean_box(0);
                            v_isShared_4255_ = v_isSharedCheck_4259_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_a_4241_ == 0 {
                    lean_del_object(v___x_4238_);
                    lean_dec(v_head_4235_);
                    v_x_4227_ = v_tail_4236_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_4239_ == 0 {
                        lean_ctor_set(v___x_4238_, 1, v_x_4228_);
                        v___x_4244_ = v___x_4238_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_head_4235_);
                        lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_x_4228_);
                        v___x_4244_ = v_reuseFailAlloc_4246_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_x_4227_ = v_tail_4236_;
                v_x_4228_ = v___x_4244_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg___boxed(
    mut v_a_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_x_4263_: *mut LeanObject,
    mut v_x_4264_: *mut LeanObject,
    mut v___y_4265_: *mut LeanObject,
    mut v___y_4266_: *mut LeanObject,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_25854__boxed_4270_: u8 = 0;
    let mut v_a_25855__boxed_4271_: u8 = 0;
    let mut v_res_4272_: *mut LeanObject = core::ptr::null_mut();
    v_a_25854__boxed_4270_ = (lean_unbox(v_a_4261_) as u8);
    v_a_25855__boxed_4271_ = (lean_unbox(v_a_4262_) as u8);
    v_res_4272_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v_a_25854__boxed_4270_, v_a_25855__boxed_4271_, v_x_4263_, v_x_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
    lean_dec(v___y_4268_);
    lean_dec_ref(v___y_4267_);
    lean_dec(v___y_4266_);
    lean_dec_ref(v___y_4265_);
    return v_res_4272_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(
    mut v_filter_4275_: *mut LeanObject,
    mut v_as_x27_4276_: *mut LeanObject,
    mut v_b_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
    mut v___y_4283_: *mut LeanObject,
    mut v___y_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_regularEqcs_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: u8 = 0;
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4344_: u8 = 0;
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4348_: u8 = 0;
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_a_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4375_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4381_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4276_) == 0 {
                    lean_dec(v_filter_4275_);
                    v___x_4289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4289_, 0, v_b_4277_);
                    return v___x_4289_;
                } else {
                    v_head_4290_ = lean_ctor_get(v_as_x27_4276_, 0);
                    v_tail_4291_ = lean_ctor_get(v_as_x27_4276_, 1);
                    v_fst_4292_ = lean_ctor_get(v_b_4277_, 0);
                    v_snd_4293_ = lean_ctor_get(v_b_4277_, 1);
                    v_isSharedCheck_4390_ = (!lean_is_exclusive(v_b_4277_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v___x_4295_ = v_b_4277_;
                        v_isShared_4296_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4293_);
                        lean_inc(v_fst_4292_);
                        lean_dec(v_b_4277_);
                        v___x_4295_ = lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4290_);
                v___x_4302_ = l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__1(v_head_4290_);
                if lean_obj_tag(v___x_4302_) == 0 {
                    lean_inc(v_head_4290_);
                    v___x_4303_ = l_List_find_x3f___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__2(v_head_4290_);
                    if lean_obj_tag(v___x_4303_) == 0 {
                        if lean_obj_tag(v_head_4290_) == 1 {
                            v_tail_4304_ = lean_ctor_get(v_head_4290_, 1);
                            if lean_obj_tag(v_tail_4304_) == 1 {
                                lean_del_object(v___x_4295_);
                                v_head_4305_ = lean_ctor_get(v_head_4290_, 0);
                                lean_inc(v_head_4305_);
                                v___x_4306_ = l_Lean_Meta_isProof(
                                    v_head_4305_,
                                    v___y_4284_,
                                    v___y_4285_,
                                    v___y_4286_,
                                    v___y_4287_,
                                );
                                if lean_obj_tag(v___x_4306_) == 0 {
                                    v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
                                    lean_inc(v_a_4307_);
                                    lean_dec_ref_known(v___x_4306_, 1);
                                    v___x_4308_ = (lean_unbox(v_a_4307_) as u8);
                                    if v___x_4308_ == 0 {
                                        lean_inc_ref(v_head_4290_);
                                        lean_inc(v_filter_4275_);
                                        v___x_4309_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_4275_, v_head_4290_, v___y_4278_, v___y_4285_);
                                        if lean_obj_tag(v___x_4309_) == 0 {
                                            v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
                                            lean_inc(v_a_4310_);
                                            lean_dec_ref_known(v___x_4309_, 1);
                                            v___x_4311_ = (lean_unbox(v_a_4310_) as u8);
                                            if v___x_4311_ == 0 {
                                                lean_dec(v_a_4310_);
                                                lean_dec(v_a_4307_);
                                                v___x_4312_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v___x_4312_, 0, v_fst_4292_);
                                                lean_ctor_set(v___x_4312_, 1, v_snd_4293_);
                                                v_as_x27_4276_ = v_tail_4291_;
                                                v_b_4277_ = v___x_4312_;
                                                state = 0;
                                                continue;
                                            } else {
                                                v_regularEqcs_4314_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0;
                                                v___x_4353_ = lean_box(0);
                                                v___x_4354_ = (lean_unbox(v_a_4310_) as u8);
                                                lean_dec(v_a_4310_);
                                                v___x_4355_ = (lean_unbox(v_a_4307_) as u8);
                                                lean_dec(v_a_4307_);
                                                lean_inc_ref(v_head_4290_);
                                                v___x_4356_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v___x_4354_, v___x_4355_, v_head_4290_, v___x_4353_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
                                                if lean_obj_tag(v___x_4356_) == 0 {
                                                    v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
                                                    lean_inc(v_a_4357_);
                                                    lean_dec_ref_known(v___x_4356_, 1);
                                                    v___x_4358_ =
                                                        l_List_reverse___redArg(v_a_4357_);
                                                    v_a_4332_ = v___x_4358_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    if lean_obj_tag(v___x_4356_) == 0 {
                                                        v_a_4359_ = lean_ctor_get(v___x_4356_, 0);
                                                        lean_inc(v_a_4359_);
                                                        lean_dec_ref_known(v___x_4356_, 1);
                                                        v_a_4332_ = v_a_4359_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        lean_dec(v_snd_4293_);
                                                        lean_dec(v_fst_4292_);
                                                        lean_dec(v_filter_4275_);
                                                        v_a_4360_ = lean_ctor_get(v___x_4356_, 0);
                                                        v_isSharedCheck_4367_ =
                                                            (!lean_is_exclusive(v___x_4356_)) as u8;
                                                        if v_isSharedCheck_4367_ == 0 {
                                                            v___x_4362_ = v___x_4356_;
                                                            v_isShared_4363_ =
                                                                v_isSharedCheck_4367_;
                                                            state = 8;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4360_);
                                                            lean_dec(v___x_4356_);
                                                            v___x_4362_ = lean_box(0);
                                                            v_isShared_4363_ =
                                                                v_isSharedCheck_4367_;
                                                            state = 8;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_4307_);
                                            lean_dec(v_snd_4293_);
                                            lean_dec(v_fst_4292_);
                                            lean_dec(v_filter_4275_);
                                            v_a_4368_ = lean_ctor_get(v___x_4309_, 0);
                                            v_isSharedCheck_4375_ =
                                                (!lean_is_exclusive(v___x_4309_)) as u8;
                                            if v_isSharedCheck_4375_ == 0 {
                                                v___x_4370_ = v___x_4309_;
                                                v_isShared_4371_ = v_isSharedCheck_4375_;
                                                state = 10;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4368_);
                                                lean_dec(v___x_4309_);
                                                v___x_4370_ = lean_box(0);
                                                v_isShared_4371_ = v_isSharedCheck_4375_;
                                                state = 10;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_4307_);
                                        v___x_4376_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_4376_, 0, v_fst_4292_);
                                        lean_ctor_set(v___x_4376_, 1, v_snd_4293_);
                                        v_as_x27_4276_ = v_tail_4291_;
                                        v_b_4277_ = v___x_4376_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_snd_4293_);
                                    lean_dec(v_fst_4292_);
                                    lean_dec(v_filter_4275_);
                                    v_a_4378_ = lean_ctor_get(v___x_4306_, 0);
                                    v_isSharedCheck_4385_ = (!lean_is_exclusive(v___x_4306_)) as u8;
                                    if v_isSharedCheck_4385_ == 0 {
                                        v___x_4380_ = v___x_4306_;
                                        v_isShared_4381_ = v_isSharedCheck_4385_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4378_);
                                        lean_dec(v___x_4306_);
                                        v___x_4380_ = lean_box(0);
                                        v_isShared_4381_ = v_isSharedCheck_4385_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_4303_, 1);
                        lean_del_object(v___x_4295_);
                        v___x_4386_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4386_, 0, v_fst_4292_);
                        lean_ctor_set(v___x_4386_, 1, v_snd_4293_);
                        v_as_x27_4276_ = v_tail_4291_;
                        v_b_4277_ = v___x_4386_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_4302_, 1);
                    lean_del_object(v___x_4295_);
                    v___x_4388_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4388_, 0, v_fst_4292_);
                    lean_ctor_set(v___x_4388_, 1, v_snd_4293_);
                    v_as_x27_4276_ = v_tail_4291_;
                    v_b_4277_ = v___x_4388_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_4296_ == 0 {
                    v___x_4299_ = v___x_4295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4301_, 0, v_fst_4292_);
                    lean_ctor_set(v_reuseFailAlloc_4301_, 1, v_snd_4293_);
                    v___x_4299_ = v_reuseFailAlloc_4301_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_as_x27_4276_ = v_tail_4291_;
                v_b_4277_ = v___x_4299_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4318_ = l_List_isEmpty___redArg(v_a_4317_);
                if v___x_4318_ == 0 {
                    v___x_4319_ = l_Lean_Meta_Grind_ppEqc(v_a_4317_, v_regularEqcs_4314_);
                    v___x_4320_ = lean_unsigned_to_nat(1);
                    v___x_4321_ = lean_mk_empty_array_with_capacity(v___x_4320_);
                    v___x_4322_ = lean_array_push(v___x_4321_, v___x_4319_);
                    v___x_4323_ = l_Lean_Meta_Grind_ppEqc(v___y_4316_, v___x_4322_);
                    v___x_4324_ = lean_array_push(v_fst_4292_, v___x_4323_);
                    v___x_4325_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4325_, 0, v___x_4324_);
                    lean_ctor_set(v___x_4325_, 1, v_snd_4293_);
                    v_as_x27_4276_ = v_tail_4291_;
                    v_b_4277_ = v___x_4325_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_4317_);
                    v___x_4327_ = l_Lean_Meta_Grind_ppEqc(v___y_4316_, v_regularEqcs_4314_);
                    v___x_4328_ = lean_array_push(v_fst_4292_, v___x_4327_);
                    v___x_4329_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4329_, 0, v___x_4328_);
                    lean_ctor_set(v___x_4329_, 1, v_snd_4293_);
                    v_as_x27_4276_ = v_tail_4291_;
                    v_b_4277_ = v___x_4329_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                v___x_4333_ = l_List_lengthTR___redArg(v_a_4332_);
                v___x_4334_ = lean_unsigned_to_nat(1);
                v___x_4335_ = lean_nat_dec_le(v___x_4333_, v___x_4334_);
                lean_dec(v___x_4333_);
                if v___x_4335_ == 0 {
                    v___x_4336_ = lean_box(0);
                    lean_inc_ref(v_head_4290_);
                    v___x_4337_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_head_4290_, v___x_4336_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
                    if lean_obj_tag(v___x_4337_) == 0 {
                        v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
                        lean_inc(v_a_4338_);
                        lean_dec_ref_known(v___x_4337_, 1);
                        v___x_4339_ = l_List_reverse___redArg(v_a_4338_);
                        v___y_4316_ = v_a_4332_;
                        v_a_4317_ = v___x_4339_;
                        state = 4;
                        continue;
                    } else {
                        if lean_obj_tag(v___x_4337_) == 0 {
                            v_a_4340_ = lean_ctor_get(v___x_4337_, 0);
                            lean_inc(v_a_4340_);
                            lean_dec_ref_known(v___x_4337_, 1);
                            v___y_4316_ = v_a_4332_;
                            v_a_4317_ = v_a_4340_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_a_4332_);
                            lean_dec(v_snd_4293_);
                            lean_dec(v_fst_4292_);
                            lean_dec(v_filter_4275_);
                            v_a_4341_ = lean_ctor_get(v___x_4337_, 0);
                            v_isSharedCheck_4348_ = (!lean_is_exclusive(v___x_4337_)) as u8;
                            if v_isSharedCheck_4348_ == 0 {
                                v___x_4343_ = v___x_4337_;
                                v_isShared_4344_ = v_isSharedCheck_4348_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4341_);
                                lean_dec(v___x_4337_);
                                v___x_4343_ = lean_box(0);
                                v_isShared_4344_ = v_isSharedCheck_4348_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_4332_);
                    lean_inc_ref(v_head_4290_);
                    v___x_4349_ = l_Lean_Meta_Grind_ppEqc(v_head_4290_, v_regularEqcs_4314_);
                    v___x_4350_ = lean_array_push(v_snd_4293_, v___x_4349_);
                    v___x_4351_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4351_, 0, v_fst_4292_);
                    lean_ctor_set(v___x_4351_, 1, v___x_4350_);
                    v_as_x27_4276_ = v_tail_4291_;
                    v_b_4277_ = v___x_4351_;
                    state = 0;
                    continue;
                }
            }
            6 => {
                if v_isShared_4344_ == 0 {
                    v___x_4346_ = v___x_4343_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4341_);
                    v___x_4346_ = v_reuseFailAlloc_4347_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4346_;
            }
            8 => {
                if v_isShared_4363_ == 0 {
                    v___x_4365_ = v___x_4362_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
                    v___x_4365_ = v_reuseFailAlloc_4366_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4365_;
            }
            10 => {
                if v_isShared_4371_ == 0 {
                    v___x_4373_ = v___x_4370_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
                    v___x_4373_ = v_reuseFailAlloc_4374_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4373_;
            }
            12 => {
                if v_isShared_4381_ == 0 {
                    v___x_4383_ = v___x_4380_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
                    v___x_4383_ = v_reuseFailAlloc_4384_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___boxed(
    mut v_filter_4391_: *mut LeanObject,
    mut v_as_x27_4392_: *mut LeanObject,
    mut v_b_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4405_: *mut LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_4391_, v_as_x27_4392_, v_b_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
    lean_dec(v___y_4403_);
    lean_dec_ref(v___y_4402_);
    lean_dec(v___y_4401_);
    lean_dec_ref(v___y_4400_);
    lean_dec(v___y_4399_);
    lean_dec_ref(v___y_4398_);
    lean_dec(v___y_4397_);
    lean_dec_ref(v___y_4396_);
    lean_dec(v___y_4395_);
    lean_dec(v___y_4394_);
    lean_dec(v_as_x27_4392_);
    return v_res_4405_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    v___x_4412_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__3;
    v___x_4413_ = l_Lean_MessageData_ofFormat(v___x_4412_);
    return v___x_4413_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    v___x_4417_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__6;
    v___x_4418_ = l_Lean_MessageData_ofFormat(v___x_4417_);
    return v___x_4418_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(
    mut v_regularEqcs_4419_: *mut LeanObject,
    mut v_filter_4420_: *mut LeanObject,
    mut v___x_4421_: *mut LeanObject,
    mut v_collapsed_4422_: u8,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_regularEqcs_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: f64 = 0.0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: u8 = 0;
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: u8 = 0;
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: f64 = 0.0;
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4470_: u8 = 0;
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4449_ = lean_st_ref_get(v___y_4423_);
                v___x_4450_ = 1;
                v___x_4451_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_4449_, v___x_4450_);
                lean_dec(v___x_4449_);
                lean_inc_ref(v_regularEqcs_4419_);
                v___x_4452_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4452_, 0, v_regularEqcs_4419_);
                lean_ctor_set(v___x_4452_, 1, v_regularEqcs_4419_);
                v___x_4453_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_4420_, v___x_4451_, v___x_4452_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
                lean_dec(v___x_4451_);
                if lean_obj_tag(v___x_4453_) == 0 {
                    v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
                    lean_inc(v_a_4454_);
                    lean_dec_ref_known(v___x_4453_, 1);
                    v_fst_4455_ = lean_ctor_get(v_a_4454_, 0);
                    lean_inc(v_fst_4455_);
                    v_snd_4456_ = lean_ctor_get(v_a_4454_, 1);
                    lean_inc(v_snd_4456_);
                    lean_dec(v_a_4454_);
                    v___x_4457_ = lean_array_get_size(v_snd_4456_);
                    v___x_4458_ = lean_nat_dec_eq(v___x_4457_, v___x_4421_);
                    if v___x_4458_ == 0 {
                        v___x_4459_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1;
                        v___x_4460_ = lean_box(0);
                        lean_inc(v___x_4421_);
                        v___x_4461_ = lean_float_of_nat(v___x_4421_);
                        v___x_4462_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
                        v___x_4463_ = lean_alloc_ctor(0, 3, (17) as u32);
                        lean_ctor_set(v___x_4463_, 0, v___x_4459_);
                        lean_ctor_set(v___x_4463_, 1, v___x_4460_);
                        lean_ctor_set(v___x_4463_, 2, v___x_4462_);
                        lean_ctor_set_float(
                            v___x_4463_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_4461_,
                        );
                        lean_ctor_set_float(
                            v___x_4463_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_4461_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4463_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v___x_4450_,
                        );
                        v___x_4464_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__7);
                        v___x_4465_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_4465_, 0, v___x_4463_);
                        lean_ctor_set(v___x_4465_, 1, v___x_4464_);
                        lean_ctor_set(v___x_4465_, 2, v_snd_4456_);
                        v___x_4466_ = lean_array_push(v_fst_4455_, v___x_4465_);
                        v_regularEqcs_4435_ = v___x_4466_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_snd_4456_);
                        v_regularEqcs_4435_ = v_fst_4455_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4421_);
                    v_a_4467_ = lean_ctor_get(v___x_4453_, 0);
                    v_isSharedCheck_4474_ = (!lean_is_exclusive(v___x_4453_)) as u8;
                    if v_isSharedCheck_4474_ == 0 {
                        v___x_4469_ = v___x_4453_;
                        v_isShared_4470_ = v_isSharedCheck_4474_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4467_);
                        lean_dec(v___x_4453_);
                        v___x_4469_ = lean_box(0);
                        v_isShared_4470_ = v_isSharedCheck_4474_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4436_ = lean_array_get_size(v_regularEqcs_4435_);
                v___x_4437_ = lean_nat_dec_eq(v___x_4436_, v___x_4421_);
                if v___x_4437_ == 0 {
                    v___x_4438_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__1;
                    v___x_4439_ = lean_box(0);
                    v___x_4440_ = lean_float_of_nat(v___x_4421_);
                    v___x_4441_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
                    v___x_4442_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v___x_4442_, 0, v___x_4438_);
                    lean_ctor_set(v___x_4442_, 1, v___x_4439_);
                    lean_ctor_set(v___x_4442_, 2, v___x_4441_);
                    lean_ctor_set_float(
                        v___x_4442_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_4440_,
                    );
                    lean_ctor_set_float(
                        v___x_4442_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_4440_,
                    );
                    lean_ctor_set_uint8(
                        v___x_4442_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v_collapsed_4422_,
                    );
                    v___x_4443_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___closed__4);
                    v___x_4444_ = lean_alloc_ctor(9, 3, (0) as u32);
                    lean_ctor_set(v___x_4444_, 0, v___x_4442_);
                    lean_ctor_set(v___x_4444_, 1, v___x_4443_);
                    lean_ctor_set(v___x_4444_, 2, v_regularEqcs_4435_);
                    v___x_4445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4445_, 0, v___x_4444_);
                    v___x_4446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4446_, 0, v___x_4445_);
                    return v___x_4446_;
                } else {
                    lean_dec_ref(v_regularEqcs_4435_);
                    lean_dec(v___x_4421_);
                    v___x_4447_ = lean_box(0);
                    v___x_4448_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4448_, 0, v___x_4447_);
                    return v___x_4448_;
                }
            }
            2 => {
                if v_isShared_4470_ == 0 {
                    v___x_4472_ = v___x_4469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed(
    mut v_regularEqcs_4475_: *mut LeanObject,
    mut v_filter_4476_: *mut LeanObject,
    mut v___x_4477_: *mut LeanObject,
    mut v_collapsed_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_4490_: u8 = 0;
    let mut v_res_4491_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4490_ = (lean_unbox(v_collapsed_4478_) as u8);
    v_res_4491_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0(v_regularEqcs_4475_, v_filter_4476_, v___x_4477_, v_collapsed_boxed_4490_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
    lean_dec(v___y_4488_);
    lean_dec_ref(v___y_4487_);
    lean_dec(v___y_4486_);
    lean_dec_ref(v___y_4485_);
    lean_dec(v___y_4484_);
    lean_dec_ref(v___y_4483_);
    lean_dec(v___y_4482_);
    lean_dec_ref(v___y_4481_);
    lean_dec(v___y_4480_);
    lean_dec(v___y_4479_);
    return v_res_4491_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(
    mut v_filter_4492_: *mut LeanObject,
    mut v_collapsed_4493_: u8,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
    mut v_a_4497_: *mut LeanObject,
    mut v_a_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_regularEqcs_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    v___x_4501_ = lean_unsigned_to_nat(0);
    v_regularEqcs_4502_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0;
    v___x_4503_ = lean_box((v_collapsed_4493_) as usize);
    v___f_4504_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 4);
    lean_closure_set(v___f_4504_, 0, v_regularEqcs_4502_);
    lean_closure_set(v___f_4504_, 1, v_filter_4492_);
    lean_closure_set(v___f_4504_, 2, v___x_4501_);
    lean_closure_set(v___f_4504_, 3, v___x_4503_);
    v___x_4505_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(
        v___f_4504_,
        v_a_4494_,
        v_a_4495_,
        v_a_4496_,
        v_a_4497_,
        v_a_4498_,
        v_a_4499_,
    );
    return v___x_4505_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg___boxed(
    mut v_filter_4506_: *mut LeanObject,
    mut v_collapsed_4507_: *mut LeanObject,
    mut v_a_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_a_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_a_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_a_4514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_4515_: u8 = 0;
    let mut v_res_4516_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4515_ = (lean_unbox(v_collapsed_4507_) as u8);
    v_res_4516_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(
            v_filter_4506_,
            v_collapsed_boxed_4515_,
            v_a_4508_,
            v_a_4509_,
            v_a_4510_,
            v_a_4511_,
            v_a_4512_,
            v_a_4513_,
        );
    lean_dec(v_a_4513_);
    lean_dec_ref(v_a_4512_);
    lean_dec(v_a_4511_);
    lean_dec_ref(v_a_4510_);
    lean_dec(v_a_4509_);
    lean_dec_ref(v_a_4508_);
    return v_res_4516_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(
    mut v_filter_4517_: *mut LeanObject,
    mut v_collapsed_4518_: u8,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
    mut v_a_4522_: *mut LeanObject,
    mut v_a_4523_: *mut LeanObject,
    mut v_a_4524_: *mut LeanObject,
    mut v_a_4525_: *mut LeanObject,
    mut v_a_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    v___x_4528_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(
            v_filter_4517_,
            v_collapsed_4518_,
            v_a_4519_,
            v_a_4520_,
            v_a_4523_,
            v_a_4524_,
            v_a_4525_,
            v_a_4526_,
        );
    return v___x_4528_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___boxed(
    mut v_filter_4529_: *mut LeanObject,
    mut v_collapsed_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_a_4532_: *mut LeanObject,
    mut v_a_4533_: *mut LeanObject,
    mut v_a_4534_: *mut LeanObject,
    mut v_a_4535_: *mut LeanObject,
    mut v_a_4536_: *mut LeanObject,
    mut v_a_4537_: *mut LeanObject,
    mut v_a_4538_: *mut LeanObject,
    mut v_a_4539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_collapsed_boxed_4540_: u8 = 0;
    let mut v_res_4541_: *mut LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_4540_ = (lean_unbox(v_collapsed_4530_) as u8);
    v_res_4541_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f(
        v_filter_4529_,
        v_collapsed_boxed_4540_,
        v_a_4531_,
        v_a_4532_,
        v_a_4533_,
        v_a_4534_,
        v_a_4535_,
        v_a_4536_,
        v_a_4537_,
        v_a_4538_,
    );
    lean_dec(v_a_4538_);
    lean_dec_ref(v_a_4537_);
    lean_dec(v_a_4536_);
    lean_dec_ref(v_a_4535_);
    lean_dec(v_a_4534_);
    lean_dec_ref(v_a_4533_);
    lean_dec(v_a_4532_);
    lean_dec_ref(v_a_4531_);
    return v_res_4541_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(
    mut v_x_4542_: *mut LeanObject,
    mut v_x_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    v___x_4555_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___redArg(v_x_4542_, v_x_4543_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
    return v___x_4555_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0___boxed(
    mut v_x_4556_: *mut LeanObject,
    mut v_x_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4569_: *mut LeanObject = core::ptr::null_mut();
    v_res_4569_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__0(v_x_4556_, v_x_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_);
    lean_dec(v___y_4567_);
    lean_dec_ref(v___y_4566_);
    lean_dec(v___y_4565_);
    lean_dec_ref(v___y_4564_);
    lean_dec(v___y_4563_);
    lean_dec_ref(v___y_4562_);
    lean_dec(v___y_4561_);
    lean_dec_ref(v___y_4560_);
    lean_dec(v___y_4559_);
    lean_dec(v___y_4558_);
    return v_res_4569_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(
    mut v_filter_4570_: *mut LeanObject,
    mut v_x_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
    mut v___y_4580_: *mut LeanObject,
    mut v___y_4581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    v___x_4583_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___redArg(v_filter_4570_, v_x_4571_, v___y_4572_, v___y_4579_);
    return v___x_4583_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3___boxed(
    mut v_filter_4584_: *mut LeanObject,
    mut v_x_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
    mut v___y_4593_: *mut LeanObject,
    mut v___y_4594_: *mut LeanObject,
    mut v___y_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4597_: *mut LeanObject = core::ptr::null_mut();
    v_res_4597_ = l_List_anyM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__3(v_filter_4584_, v_x_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
    lean_dec(v___y_4595_);
    lean_dec_ref(v___y_4594_);
    lean_dec(v___y_4593_);
    lean_dec_ref(v___y_4592_);
    lean_dec(v___y_4591_);
    lean_dec_ref(v___y_4590_);
    lean_dec(v___y_4589_);
    lean_dec_ref(v___y_4588_);
    lean_dec(v___y_4587_);
    lean_dec(v___y_4586_);
    return v_res_4597_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4(
    mut v_a_4598_: u8,
    mut v_a_4599_: u8,
    mut v_x_4600_: *mut LeanObject,
    mut v_x_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
    mut v___y_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
    mut v___y_4610_: *mut LeanObject,
    mut v___y_4611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    v___x_4613_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___redArg(v_a_4598_, v_a_4599_, v_x_4600_, v_x_4601_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
    return v___x_4613_;
}
pub unsafe fn l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4___boxed(
    mut v_a_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v_x_4616_: *mut LeanObject,
    mut v_x_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
    mut v___y_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_26425__boxed_4629_: u8 = 0;
    let mut v_a_26426__boxed_4630_: u8 = 0;
    let mut v_res_4631_: *mut LeanObject = core::ptr::null_mut();
    v_a_26425__boxed_4629_ = (lean_unbox(v_a_4614_) as u8);
    v_a_26426__boxed_4630_ = (lean_unbox(v_a_4615_) as u8);
    v_res_4631_ = l_List_filterAuxM___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__4(v_a_26425__boxed_4629_, v_a_26426__boxed_4630_, v_x_4616_, v_x_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
    lean_dec(v___y_4627_);
    lean_dec_ref(v___y_4626_);
    lean_dec(v___y_4625_);
    lean_dec_ref(v___y_4624_);
    lean_dec(v___y_4623_);
    lean_dec_ref(v___y_4622_);
    lean_dec(v___y_4621_);
    lean_dec_ref(v___y_4620_);
    lean_dec(v___y_4619_);
    lean_dec(v___y_4618_);
    return v_res_4631_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5(
    mut v_filter_4632_: *mut LeanObject,
    mut v_as_4633_: *mut LeanObject,
    mut v_as_x27_4634_: *mut LeanObject,
    mut v_b_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
    mut v___y_4643_: *mut LeanObject,
    mut v___y_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    v___x_4648_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg(v_filter_4632_, v_as_x27_4634_, v_b_4635_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
    return v___x_4648_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___boxed(
    mut v_filter_4649_: *mut LeanObject,
    mut v_as_4650_: *mut LeanObject,
    mut v_as_x27_4651_: *mut LeanObject,
    mut v_b_4652_: *mut LeanObject,
    mut v_a_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4665_: *mut LeanObject = core::ptr::null_mut();
    v_res_4665_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5(v_filter_4649_, v_as_4650_, v_as_x27_4651_, v_b_4652_, v_a_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
    lean_dec(v___y_4663_);
    lean_dec_ref(v___y_4662_);
    lean_dec(v___y_4661_);
    lean_dec_ref(v___y_4660_);
    lean_dec(v___y_4659_);
    lean_dec_ref(v___y_4658_);
    lean_dec(v___y_4657_);
    lean_dec_ref(v___y_4656_);
    lean_dec(v___y_4655_);
    lean_dec(v___y_4654_);
    lean_dec(v_as_x27_4651_);
    lean_dec(v_as_4650_);
    return v_res_4665_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__0;
    v___x_4668_ = l_Lean_stringToMessageData(v___x_4667_);
    return v___x_4668_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(
    mut v___x_4669_: u8,
    mut v_stx_4670_: *mut LeanObject,
    mut v___x_4671_: *mut LeanObject,
    mut v___x_4672_: *mut LeanObject,
    mut v___x_4673_: *mut LeanObject,
    mut v___x_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
    mut v___y_4678_: *mut LeanObject,
    mut v___y_4679_: *mut LeanObject,
    mut v___y_4680_: *mut LeanObject,
    mut v___y_4681_: *mut LeanObject,
    mut v___y_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_x3f_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4706_: u8 = 0;
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4710_: u8 = 0;
    let mut v_a_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4714_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4718_: u8 = 0;
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_4669_ == 0 {
                    lean_dec_ref(v___x_4674_);
                    lean_dec_ref(v___x_4673_);
                    lean_dec_ref(v___x_4672_);
                    lean_dec_ref(v___x_4671_);
                    v___x_4719_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_4719_;
                } else {
                    v___x_4720_ = lean_unsigned_to_nat(1);
                    v___x_4721_ = l_Lean_Syntax_getArg(v_stx_4670_, v___x_4720_);
                    v___x_4722_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2;
                    v___x_4723_ = l_Lean_Name_mkStr5(
                        v___x_4671_,
                        v___x_4672_,
                        v___x_4673_,
                        v___x_4674_,
                        v___x_4722_,
                    );
                    lean_inc(v___x_4721_);
                    v___x_4724_ = l_Lean_Syntax_isOfKind(v___x_4721_, v___x_4723_);
                    lean_dec(v___x_4723_);
                    if v___x_4724_ == 0 {
                        lean_dec(v___x_4721_);
                        v___x_4725_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_4725_;
                    } else {
                        v___x_4726_ = lean_unsigned_to_nat(0);
                        v___x_4727_ = l_Lean_Syntax_getArg(v___x_4721_, v___x_4726_);
                        lean_dec(v___x_4721_);
                        v___x_4728_ = l_Lean_Syntax_isNone(v___x_4727_);
                        if v___x_4728_ == 0 {
                            lean_inc(v___x_4727_);
                            v___x_4729_ = l_Lean_Syntax_matchesNull(v___x_4727_, v___x_4720_);
                            if v___x_4729_ == 0 {
                                lean_dec(v___x_4727_);
                                v___x_4730_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                                return v___x_4730_;
                            } else {
                                v_filter_x3f_4731_ = l_Lean_Syntax_getArg(v___x_4727_, v___x_4726_);
                                lean_dec(v___x_4727_);
                                v___x_4732_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4732_, 0, v_filter_x3f_4731_);
                                v_filter_x3f_4685_ = v___x_4732_;
                                v___y_4686_ = v___y_4675_;
                                v___y_4687_ = v___y_4676_;
                                v___y_4688_ = v___y_4677_;
                                v___y_4689_ = v___y_4678_;
                                v___y_4690_ = v___y_4679_;
                                v___y_4691_ = v___y_4680_;
                                v___y_4692_ = v___y_4681_;
                                v___y_4693_ = v___y_4682_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4727_);
                            v___x_4733_ = lean_box(0);
                            v_filter_x3f_4685_ = v___x_4733_;
                            v___y_4686_ = v___y_4675_;
                            v___y_4687_ = v___y_4676_;
                            v___y_4688_ = v___y_4677_;
                            v___y_4689_ = v___y_4678_;
                            v___y_4690_ = v___y_4679_;
                            v___y_4691_ = v___y_4680_;
                            v___y_4692_ = v___y_4681_;
                            v___y_4693_ = v___y_4682_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4694_ = l_Lean_Elab_Tactic_Grind_elabFilter(
                    v_filter_x3f_4685_,
                    v___y_4686_,
                    v___y_4687_,
                    v___y_4688_,
                    v___y_4689_,
                    v___y_4690_,
                    v___y_4691_,
                    v___y_4692_,
                    v___y_4693_,
                );
                if lean_obj_tag(v___x_4694_) == 0 {
                    v_a_4695_ = lean_ctor_get(v___x_4694_, 0);
                    lean_inc(v_a_4695_);
                    lean_dec_ref_known(v___x_4694_, 1);
                    v___x_4696_ = 0;
                    v___x_4697_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_a_4695_, v___x_4696_, v___y_4686_, v___y_4687_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
                    if lean_obj_tag(v___x_4697_) == 0 {
                        v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
                        lean_inc(v_a_4698_);
                        lean_dec_ref_known(v___x_4697_, 1);
                        if lean_obj_tag(v_a_4698_) == 1 {
                            v_val_4699_ = lean_ctor_get(v_a_4698_, 0);
                            lean_inc(v_val_4699_);
                            lean_dec_ref_known(v_a_4698_, 1);
                            v___x_4700_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v_val_4699_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
                            return v___x_4700_;
                        } else {
                            lean_dec(v_a_4698_);
                            v___x_4701_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___closed__1);
                            v___x_4702_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_4701_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
                            return v___x_4702_;
                        }
                    } else {
                        v_a_4703_ = lean_ctor_get(v___x_4697_, 0);
                        v_isSharedCheck_4710_ = (!lean_is_exclusive(v___x_4697_)) as u8;
                        if v_isSharedCheck_4710_ == 0 {
                            v___x_4705_ = v___x_4697_;
                            v_isShared_4706_ = v_isSharedCheck_4710_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4703_);
                            lean_dec(v___x_4697_);
                            v___x_4705_ = lean_box(0);
                            v_isShared_4706_ = v_isSharedCheck_4710_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_4711_ = lean_ctor_get(v___x_4694_, 0);
                    v_isSharedCheck_4718_ = (!lean_is_exclusive(v___x_4694_)) as u8;
                    if v_isSharedCheck_4718_ == 0 {
                        v___x_4713_ = v___x_4694_;
                        v_isShared_4714_ = v_isSharedCheck_4718_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4711_);
                        lean_dec(v___x_4694_);
                        v___x_4713_ = lean_box(0);
                        v_isShared_4714_ = v_isSharedCheck_4718_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4706_ == 0 {
                    v___x_4708_ = v___x_4705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
                    v___x_4708_ = v_reuseFailAlloc_4709_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4708_;
            }
            4 => {
                if v_isShared_4714_ == 0 {
                    v___x_4716_ = v___x_4713_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
                    v___x_4716_ = v_reuseFailAlloc_4717_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4716_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed(
    mut v___x_4734_: *mut LeanObject,
    mut v_stx_4735_: *mut LeanObject,
    mut v___x_4736_: *mut LeanObject,
    mut v___x_4737_: *mut LeanObject,
    mut v___x_4738_: *mut LeanObject,
    mut v___x_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
    mut v___y_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172__boxed_4749_: u8 = 0;
    let mut v_res_4750_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172__boxed_4749_ = (lean_unbox(v___x_4734_) as u8);
    v_res_4750_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0(v___x_1172__boxed_4749_, v_stx_4735_, v___x_4736_, v___x_4737_, v___x_4738_, v___x_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
    lean_dec(v___y_4747_);
    lean_dec_ref(v___y_4746_);
    lean_dec(v___y_4745_);
    lean_dec_ref(v___y_4744_);
    lean_dec(v___y_4743_);
    lean_dec_ref(v___y_4742_);
    lean_dec(v___y_4741_);
    lean_dec_ref(v___y_4740_);
    lean_dec(v_stx_4735_);
    return v_res_4750_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(
    mut v_stx_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_a_4762_: *mut LeanObject,
    mut v_a_4763_: *mut LeanObject,
    mut v_a_4764_: *mut LeanObject,
    mut v_a_4765_: *mut LeanObject,
    mut v_a_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    v___x_4768_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0;
    v___x_4769_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1;
    v___x_4770_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
    v___x_4771_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2;
    v___x_4772_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1;
    lean_inc(v_stx_4758_);
    v___x_4773_ = l_Lean_Syntax_isOfKind(v_stx_4758_, v___x_4772_);
    v___x_4774_ = lean_box((v___x_4773_) as usize);
    v___y_4775_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___lam__0___boxed as *mut core::ffi::c_void, 15, 6);
    lean_closure_set(v___y_4775_, 0, v___x_4774_);
    lean_closure_set(v___y_4775_, 1, v_stx_4758_);
    lean_closure_set(v___y_4775_, 2, v___x_4768_);
    lean_closure_set(v___y_4775_, 3, v___x_4769_);
    lean_closure_set(v___y_4775_, 4, v___x_4770_);
    lean_closure_set(v___y_4775_, 5, v___x_4771_);
    v___x_4776_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_4775_,
        v_a_4759_,
        v_a_4760_,
        v_a_4761_,
        v_a_4762_,
        v_a_4763_,
        v_a_4764_,
        v_a_4765_,
        v_a_4766_,
    );
    return v___x_4776_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed(
    mut v_stx_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_a_4781_: *mut LeanObject,
    mut v_a_4782_: *mut LeanObject,
    mut v_a_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_a_4785_: *mut LeanObject,
    mut v_a_4786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4787_: *mut LeanObject = core::ptr::null_mut();
    v_res_4787_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs(
            v_stx_4777_,
            v_a_4778_,
            v_a_4779_,
            v_a_4780_,
            v_a_4781_,
            v_a_4782_,
            v_a_4783_,
            v_a_4784_,
            v_a_4785_,
        );
    lean_dec(v_a_4785_);
    lean_dec_ref(v_a_4784_);
    lean_dec(v_a_4783_);
    lean_dec_ref(v_a_4782_);
    lean_dec(v_a_4781_);
    lean_dec_ref(v_a_4780_);
    lean_dec(v_a_4779_);
    lean_dec_ref(v_a_4778_);
    return v_res_4787_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1()
-> *mut LeanObject {
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v___x_4793_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_4794_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___closed__1;
    v___x_4795_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___closed__1;
    v___x_4796_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4797_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4793_,
        v___x_4794_,
        v___x_4795_,
        v___x_4796_,
    );
    return v___x_4797_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1___boxed(
    mut v_a_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4799_: *mut LeanObject = core::ptr::null_mut();
    v_res_4799_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
    return v_res_4799_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(
    mut v_msgs_4800_: *mut LeanObject,
    mut v_msg_x3f_4801_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_msg_x3f_4801_) == 1 {
        let mut v_val_4802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
        v_val_4802_ = lean_ctor_get(v_msg_x3f_4801_, 0);
        lean_inc(v_val_4802_);
        lean_dec_ref_known(v_msg_x3f_4801_, 1);
        v___x_4803_ = lean_array_push(v_msgs_4800_, v_val_4802_);
        return v___x_4803_;
    } else {
        lean_dec(v_msg_x3f_4801_);
        return v_msgs_4800_;
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2() -> f64 {
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: f64 = 0.0;
    v___x_4807_ = lean_unsigned_to_nat(0);
    v___x_4808_ = lean_float_of_nat(v___x_4807_);
    return v___x_4808_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: f64 = 0.0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    v___x_4809_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_4810_ = 0;
    v___x_4811_ = lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2,
    );
    v___x_4812_ = lean_box(0);
    v___x_4813_ = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__1;
    v___x_4814_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_4814_, 0, v___x_4813_);
    lean_ctor_set(v___x_4814_, 1, v___x_4812_);
    lean_ctor_set(v___x_4814_, 2, v___x_4809_);
    lean_ctor_set_float(
        v___x_4814_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4811_,
    );
    lean_ctor_set_float(
        v___x_4814_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_4811_,
    );
    lean_ctor_set_uint8(
        v___x_4814_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_4810_,
    );
    return v___x_4814_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    v___x_4818_ = l_Lean_Elab_Tactic_Grind_showState___redArg___closed__5;
    v___x_4819_ = l_Lean_MessageData_ofFormat(v___x_4818_);
    return v___x_4819_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_showState___redArg(
    mut v_filter_4820_: *mut LeanObject,
    mut v_isSilent_4821_: u8,
    mut v_a_4822_: *mut LeanObject,
    mut v_a_4823_: *mut LeanObject,
    mut v_a_4824_: *mut LeanObject,
    mut v_a_4825_: *mut LeanObject,
    mut v_a_4826_: *mut LeanObject,
    mut v_a_4827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4829_: u8 = 0;
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: u8 = 0;
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgs_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut v_a_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_a_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4873_: u8 = 0;
    let mut v_a_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4877_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4829_ = 1;
                lean_inc(v_filter_4820_);
                v___x_4830_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppAsserted_x3f___redArg(v_filter_4820_, v___x_4829_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
                if lean_obj_tag(v___x_4830_) == 0 {
                    v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
                    lean_inc(v_a_4831_);
                    lean_dec_ref_known(v___x_4830_, 1);
                    v___x_4832_ = 0;
                    lean_inc(v_filter_4820_);
                    v___x_4833_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_4820_, v___x_4829_, v___x_4832_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
                    if lean_obj_tag(v___x_4833_) == 0 {
                        v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
                        lean_inc(v_a_4834_);
                        lean_dec_ref_known(v___x_4833_, 1);
                        lean_inc(v_filter_4820_);
                        v___x_4835_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppProps_x3f___redArg(v_filter_4820_, v___x_4832_, v___x_4832_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
                        if lean_obj_tag(v___x_4835_) == 0 {
                            v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
                            lean_inc(v_a_4836_);
                            lean_dec_ref_known(v___x_4835_, 1);
                            v___x_4837_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f___redArg(v_filter_4820_, v___x_4832_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
                            if lean_obj_tag(v___x_4837_) == 0 {
                                v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
                                lean_inc(v_a_4838_);
                                lean_dec_ref_known(v___x_4837_, 1);
                                v_ref_4839_ = lean_ctor_get(v_a_4826_, 5);
                                v_msgs_4840_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0;
                                v___x_4841_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v_msgs_4840_, v_a_4831_);
                                v___x_4842_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_4841_, v_a_4834_);
                                v___x_4843_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_4842_, v_a_4836_);
                                v___x_4844_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_pushIfSome(v___x_4843_, v_a_4838_);
                                v___x_4845_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3_once), _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__3);
                                v___x_4846_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6_once), _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__6);
                                v___x_4847_ = lean_alloc_ctor(9, 3, (0) as u32);
                                lean_ctor_set(v___x_4847_, 0, v___x_4845_);
                                lean_ctor_set(v___x_4847_, 1, v___x_4846_);
                                lean_ctor_set(v___x_4847_, 2, v___x_4844_);
                                v___x_4848_ = 0;
                                v___x_4849_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg(v_ref_4839_, v___x_4847_, v___x_4848_, v_isSilent_4821_, v_a_4824_, v_a_4825_, v_a_4826_, v_a_4827_);
                                return v___x_4849_;
                            } else {
                                lean_dec(v_a_4836_);
                                lean_dec(v_a_4834_);
                                lean_dec(v_a_4831_);
                                v_a_4850_ = lean_ctor_get(v___x_4837_, 0);
                                v_isSharedCheck_4857_ = (!lean_is_exclusive(v___x_4837_)) as u8;
                                if v_isSharedCheck_4857_ == 0 {
                                    v___x_4852_ = v___x_4837_;
                                    v_isShared_4853_ = v_isSharedCheck_4857_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_4850_);
                                    lean_dec(v___x_4837_);
                                    v___x_4852_ = lean_box(0);
                                    v_isShared_4853_ = v_isSharedCheck_4857_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4834_);
                            lean_dec(v_a_4831_);
                            lean_dec(v_filter_4820_);
                            v_a_4858_ = lean_ctor_get(v___x_4835_, 0);
                            v_isSharedCheck_4865_ = (!lean_is_exclusive(v___x_4835_)) as u8;
                            if v_isSharedCheck_4865_ == 0 {
                                v___x_4860_ = v___x_4835_;
                                v_isShared_4861_ = v_isSharedCheck_4865_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4858_);
                                lean_dec(v___x_4835_);
                                v___x_4860_ = lean_box(0);
                                v_isShared_4861_ = v_isSharedCheck_4865_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4831_);
                        lean_dec(v_filter_4820_);
                        v_a_4866_ = lean_ctor_get(v___x_4833_, 0);
                        v_isSharedCheck_4873_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                        if v_isSharedCheck_4873_ == 0 {
                            v___x_4868_ = v___x_4833_;
                            v_isShared_4869_ = v_isSharedCheck_4873_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4866_);
                            lean_dec(v___x_4833_);
                            v___x_4868_ = lean_box(0);
                            v_isShared_4869_ = v_isSharedCheck_4873_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_filter_4820_);
                    v_a_4874_ = lean_ctor_get(v___x_4830_, 0);
                    v_isSharedCheck_4881_ = (!lean_is_exclusive(v___x_4830_)) as u8;
                    if v_isSharedCheck_4881_ == 0 {
                        v___x_4876_ = v___x_4830_;
                        v_isShared_4877_ = v_isSharedCheck_4881_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4874_);
                        lean_dec(v___x_4830_);
                        v___x_4876_ = lean_box(0);
                        v_isShared_4877_ = v_isSharedCheck_4881_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4853_ == 0 {
                    v___x_4855_ = v___x_4852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
                    v___x_4855_ = v_reuseFailAlloc_4856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4855_;
            }
            3 => {
                if v_isShared_4861_ == 0 {
                    v___x_4863_ = v___x_4860_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
                    v___x_4863_ = v_reuseFailAlloc_4864_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4863_;
            }
            5 => {
                if v_isShared_4869_ == 0 {
                    v___x_4871_ = v___x_4868_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
                    v___x_4871_ = v_reuseFailAlloc_4872_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4871_;
            }
            7 => {
                if v_isShared_4877_ == 0 {
                    v___x_4879_ = v___x_4876_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
                    v___x_4879_ = v_reuseFailAlloc_4880_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_showState___redArg___boxed(
    mut v_filter_4882_: *mut LeanObject,
    mut v_isSilent_4883_: *mut LeanObject,
    mut v_a_4884_: *mut LeanObject,
    mut v_a_4885_: *mut LeanObject,
    mut v_a_4886_: *mut LeanObject,
    mut v_a_4887_: *mut LeanObject,
    mut v_a_4888_: *mut LeanObject,
    mut v_a_4889_: *mut LeanObject,
    mut v_a_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isSilent_boxed_4891_: u8 = 0;
    let mut v_res_4892_: *mut LeanObject = core::ptr::null_mut();
    v_isSilent_boxed_4891_ = (lean_unbox(v_isSilent_4883_) as u8);
    v_res_4892_ = l_Lean_Elab_Tactic_Grind_showState___redArg(
        v_filter_4882_,
        v_isSilent_boxed_4891_,
        v_a_4884_,
        v_a_4885_,
        v_a_4886_,
        v_a_4887_,
        v_a_4888_,
        v_a_4889_,
    );
    lean_dec(v_a_4889_);
    lean_dec_ref(v_a_4888_);
    lean_dec(v_a_4887_);
    lean_dec_ref(v_a_4886_);
    lean_dec(v_a_4885_);
    lean_dec_ref(v_a_4884_);
    return v_res_4892_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_showState(
    mut v_filter_4893_: *mut LeanObject,
    mut v_isSilent_4894_: u8,
    mut v_a_4895_: *mut LeanObject,
    mut v_a_4896_: *mut LeanObject,
    mut v_a_4897_: *mut LeanObject,
    mut v_a_4898_: *mut LeanObject,
    mut v_a_4899_: *mut LeanObject,
    mut v_a_4900_: *mut LeanObject,
    mut v_a_4901_: *mut LeanObject,
    mut v_a_4902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    v___x_4904_ = l_Lean_Elab_Tactic_Grind_showState___redArg(
        v_filter_4893_,
        v_isSilent_4894_,
        v_a_4895_,
        v_a_4896_,
        v_a_4899_,
        v_a_4900_,
        v_a_4901_,
        v_a_4902_,
    );
    return v___x_4904_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_showState___boxed(
    mut v_filter_4905_: *mut LeanObject,
    mut v_isSilent_4906_: *mut LeanObject,
    mut v_a_4907_: *mut LeanObject,
    mut v_a_4908_: *mut LeanObject,
    mut v_a_4909_: *mut LeanObject,
    mut v_a_4910_: *mut LeanObject,
    mut v_a_4911_: *mut LeanObject,
    mut v_a_4912_: *mut LeanObject,
    mut v_a_4913_: *mut LeanObject,
    mut v_a_4914_: *mut LeanObject,
    mut v_a_4915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isSilent_boxed_4916_: u8 = 0;
    let mut v_res_4917_: *mut LeanObject = core::ptr::null_mut();
    v_isSilent_boxed_4916_ = (lean_unbox(v_isSilent_4906_) as u8);
    v_res_4917_ = l_Lean_Elab_Tactic_Grind_showState(
        v_filter_4905_,
        v_isSilent_boxed_4916_,
        v_a_4907_,
        v_a_4908_,
        v_a_4909_,
        v_a_4910_,
        v_a_4911_,
        v_a_4912_,
        v_a_4913_,
        v_a_4914_,
    );
    lean_dec(v_a_4914_);
    lean_dec_ref(v_a_4913_);
    lean_dec(v_a_4912_);
    lean_dec_ref(v_a_4911_);
    lean_dec(v_a_4910_);
    lean_dec_ref(v_a_4909_);
    lean_dec(v_a_4908_);
    lean_dec_ref(v_a_4907_);
    return v_res_4917_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(
    mut v___x_4918_: u8,
    mut v_stx_4919_: *mut LeanObject,
    mut v___x_4920_: *mut LeanObject,
    mut v___x_4921_: *mut LeanObject,
    mut v___x_4922_: *mut LeanObject,
    mut v___x_4923_: *mut LeanObject,
    mut v___y_4924_: *mut LeanObject,
    mut v___y_4925_: *mut LeanObject,
    mut v___y_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
    mut v___y_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_filter_x3f_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: u8 = 0;
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4950_: u8 = 0;
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: u8 = 0;
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: u8 = 0;
    let mut v___x_4965_: u8 = 0;
    let mut v___x_4966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_4918_ == 0 {
                    lean_dec_ref(v___x_4923_);
                    lean_dec_ref(v___x_4922_);
                    lean_dec_ref(v___x_4921_);
                    lean_dec_ref(v___x_4920_);
                    v___x_4955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_4955_;
                } else {
                    v___x_4956_ = lean_unsigned_to_nat(1);
                    v___x_4957_ = l_Lean_Syntax_getArg(v_stx_4919_, v___x_4956_);
                    v___x_4958_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2;
                    v___x_4959_ = l_Lean_Name_mkStr5(
                        v___x_4920_,
                        v___x_4921_,
                        v___x_4922_,
                        v___x_4923_,
                        v___x_4958_,
                    );
                    lean_inc(v___x_4957_);
                    v___x_4960_ = l_Lean_Syntax_isOfKind(v___x_4957_, v___x_4959_);
                    lean_dec(v___x_4959_);
                    if v___x_4960_ == 0 {
                        lean_dec(v___x_4957_);
                        v___x_4961_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_4961_;
                    } else {
                        v___x_4962_ = lean_unsigned_to_nat(0);
                        v___x_4963_ = l_Lean_Syntax_getArg(v___x_4957_, v___x_4962_);
                        lean_dec(v___x_4957_);
                        v___x_4964_ = l_Lean_Syntax_isNone(v___x_4963_);
                        if v___x_4964_ == 0 {
                            lean_inc(v___x_4963_);
                            v___x_4965_ = l_Lean_Syntax_matchesNull(v___x_4963_, v___x_4956_);
                            if v___x_4965_ == 0 {
                                lean_dec(v___x_4963_);
                                v___x_4966_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                                return v___x_4966_;
                            } else {
                                v_filter_x3f_4967_ = l_Lean_Syntax_getArg(v___x_4963_, v___x_4962_);
                                lean_dec(v___x_4963_);
                                v___x_4968_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4968_, 0, v_filter_x3f_4967_);
                                v_filter_x3f_4934_ = v___x_4968_;
                                v___y_4935_ = v___y_4924_;
                                v___y_4936_ = v___y_4925_;
                                v___y_4937_ = v___y_4926_;
                                v___y_4938_ = v___y_4927_;
                                v___y_4939_ = v___y_4928_;
                                v___y_4940_ = v___y_4929_;
                                v___y_4941_ = v___y_4930_;
                                v___y_4942_ = v___y_4931_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4963_);
                            v___x_4969_ = lean_box(0);
                            v_filter_x3f_4934_ = v___x_4969_;
                            v___y_4935_ = v___y_4924_;
                            v___y_4936_ = v___y_4925_;
                            v___y_4937_ = v___y_4926_;
                            v___y_4938_ = v___y_4927_;
                            v___y_4939_ = v___y_4928_;
                            v___y_4940_ = v___y_4929_;
                            v___y_4941_ = v___y_4930_;
                            v___y_4942_ = v___y_4931_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4943_ = l_Lean_Elab_Tactic_Grind_elabFilter(
                    v_filter_x3f_4934_,
                    v___y_4935_,
                    v___y_4936_,
                    v___y_4937_,
                    v___y_4938_,
                    v___y_4939_,
                    v___y_4940_,
                    v___y_4941_,
                    v___y_4942_,
                );
                if lean_obj_tag(v___x_4943_) == 0 {
                    v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
                    lean_inc(v_a_4944_);
                    lean_dec_ref_known(v___x_4943_, 1);
                    v___x_4945_ = 0;
                    v___x_4946_ = l_Lean_Elab_Tactic_Grind_showState___redArg(
                        v_a_4944_,
                        v___x_4945_,
                        v___y_4935_,
                        v___y_4936_,
                        v___y_4939_,
                        v___y_4940_,
                        v___y_4941_,
                        v___y_4942_,
                    );
                    return v___x_4946_;
                } else {
                    v_a_4947_ = lean_ctor_get(v___x_4943_, 0);
                    v_isSharedCheck_4954_ = (!lean_is_exclusive(v___x_4943_)) as u8;
                    if v_isSharedCheck_4954_ == 0 {
                        v___x_4949_ = v___x_4943_;
                        v_isShared_4950_ = v_isSharedCheck_4954_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4947_);
                        lean_dec(v___x_4943_);
                        v___x_4949_ = lean_box(0);
                        v_isShared_4950_ = v_isSharedCheck_4954_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4950_ == 0 {
                    v___x_4952_ = v___x_4949_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
                    v___x_4952_ = v_reuseFailAlloc_4953_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed(
    mut v___x_4970_: *mut LeanObject,
    mut v_stx_4971_: *mut LeanObject,
    mut v___x_4972_: *mut LeanObject,
    mut v___x_4973_: *mut LeanObject,
    mut v___x_4974_: *mut LeanObject,
    mut v___x_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
    mut v___y_4982_: *mut LeanObject,
    mut v___y_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_553__boxed_4985_: u8 = 0;
    let mut v_res_4986_: *mut LeanObject = core::ptr::null_mut();
    v___x_553__boxed_4985_ = (lean_unbox(v___x_4970_) as u8);
    v_res_4986_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0(v___x_553__boxed_4985_, v_stx_4971_, v___x_4972_, v___x_4973_, v___x_4974_, v___x_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_);
    lean_dec(v___y_4983_);
    lean_dec_ref(v___y_4982_);
    lean_dec(v___y_4981_);
    lean_dec_ref(v___y_4980_);
    lean_dec(v___y_4979_);
    lean_dec_ref(v___y_4978_);
    lean_dec(v___y_4977_);
    lean_dec_ref(v___y_4976_);
    lean_dec(v_stx_4971_);
    return v_res_4986_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(
    mut v_stx_4994_: *mut LeanObject,
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
    mut v_a_4997_: *mut LeanObject,
    mut v_a_4998_: *mut LeanObject,
    mut v_a_4999_: *mut LeanObject,
    mut v_a_5000_: *mut LeanObject,
    mut v_a_5001_: *mut LeanObject,
    mut v_a_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: u8 = 0;
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    v___x_5004_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0;
    v___x_5005_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1;
    v___x_5006_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
    v___x_5007_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2;
    v___x_5008_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1;
    lean_inc(v_stx_4994_);
    v___x_5009_ = l_Lean_Syntax_isOfKind(v_stx_4994_, v___x_5008_);
    v___x_5010_ = lean_box((v___x_5009_) as usize);
    v___y_5011_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___lam__0___boxed as *mut core::ffi::c_void, 15, 6);
    lean_closure_set(v___y_5011_, 0, v___x_5010_);
    lean_closure_set(v___y_5011_, 1, v_stx_4994_);
    lean_closure_set(v___y_5011_, 2, v___x_5004_);
    lean_closure_set(v___y_5011_, 3, v___x_5005_);
    lean_closure_set(v___y_5011_, 4, v___x_5006_);
    lean_closure_set(v___y_5011_, 5, v___x_5007_);
    v___x_5012_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_5011_,
        v_a_4995_,
        v_a_4996_,
        v_a_4997_,
        v_a_4998_,
        v_a_4999_,
        v_a_5000_,
        v_a_5001_,
        v_a_5002_,
    );
    return v___x_5012_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed(
    mut v_stx_5013_: *mut LeanObject,
    mut v_a_5014_: *mut LeanObject,
    mut v_a_5015_: *mut LeanObject,
    mut v_a_5016_: *mut LeanObject,
    mut v_a_5017_: *mut LeanObject,
    mut v_a_5018_: *mut LeanObject,
    mut v_a_5019_: *mut LeanObject,
    mut v_a_5020_: *mut LeanObject,
    mut v_a_5021_: *mut LeanObject,
    mut v_a_5022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5023_: *mut LeanObject = core::ptr::null_mut();
    v_res_5023_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState(
            v_stx_5013_,
            v_a_5014_,
            v_a_5015_,
            v_a_5016_,
            v_a_5017_,
            v_a_5018_,
            v_a_5019_,
            v_a_5020_,
            v_a_5021_,
        );
    lean_dec(v_a_5021_);
    lean_dec_ref(v_a_5020_);
    lean_dec(v_a_5019_);
    lean_dec_ref(v_a_5018_);
    lean_dec(v_a_5017_);
    lean_dec_ref(v_a_5016_);
    lean_dec(v_a_5015_);
    lean_dec_ref(v_a_5014_);
    return v_res_5023_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1()
-> *mut LeanObject {
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    v___x_5029_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_5030_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___closed__1;
    v___x_5031_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___closed__1;
    v___x_5032_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5033_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5029_,
        v___x_5030_,
        v___x_5031_,
        v___x_5032_,
    );
    return v___x_5033_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1___boxed(
    mut v_a_5034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5035_: *mut LeanObject = core::ptr::null_mut();
    v_res_5035_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
    return v_res_5035_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    v___x_5040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__2;
    v___x_5041_ = l_Lean_stringToMessageData(v___x_5040_);
    return v___x_5041_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    v___x_5043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__4;
    v___x_5044_ = l_Lean_stringToMessageData(v___x_5043_);
    return v___x_5044_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(
    mut v_numDigits_5045_: *mut LeanObject,
    mut v_sz_5046_: usize,
    mut v_i_5047_: usize,
    mut v_bs_5048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5049_: u8 = 0;
    let mut v_v_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchor_5052_: u64 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: f64 = 0.0;
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: usize = 0;
    let mut v___x_5071_: usize = 0;
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5049_ = lean_usize_dec_lt(v_i_5047_, v_sz_5046_);
                if v___x_5049_ == 0 {
                    return v_bs_5048_;
                } else {
                    v_v_5050_ = lean_array_uget_borrowed(v_bs_5048_, v_i_5047_);
                    v_e_5051_ = lean_ctor_get(v_v_5050_, 2);
                    lean_inc_ref(v_e_5051_);
                    v_anchor_5052_ = lean_ctor_get_uint64(
                        v_v_5050_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v___x_5053_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5054_ = lean_array_uset(v_bs_5048_, v_i_5047_, v___x_5053_);
                    v___x_5055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__1;
                    v___x_5056_ = lean_box(0);
                    v___x_5057_ = lean_float_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2,
                    );
                    v___x_5058_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
                    v___x_5059_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v___x_5059_, 0, v___x_5055_);
                    lean_ctor_set(v___x_5059_, 1, v___x_5056_);
                    lean_ctor_set(v___x_5059_, 2, v___x_5058_);
                    lean_ctor_set_float(
                        v___x_5059_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_5057_,
                    );
                    lean_ctor_set_float(
                        v___x_5059_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_5057_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5059_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v___x_5049_,
                    );
                    v___x_5060_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3);
                    v___x_5061_ =
                        l_Lean_Meta_Grind_anchorToString(v_numDigits_5045_, v_anchor_5052_);
                    v___x_5062_ = l_Lean_stringToMessageData(v___x_5061_);
                    v___x_5063_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5063_, 0, v___x_5060_);
                    lean_ctor_set(v___x_5063_, 1, v___x_5062_);
                    v___x_5064_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5);
                    v___x_5065_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5065_, 0, v___x_5063_);
                    lean_ctor_set(v___x_5065_, 1, v___x_5064_);
                    v___x_5066_ = l_Lean_MessageData_ofExpr(v_e_5051_);
                    v___x_5067_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5067_, 0, v___x_5065_);
                    lean_ctor_set(v___x_5067_, 1, v___x_5066_);
                    v___x_5068_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0;
                    v___x_5069_ = lean_alloc_ctor(9, 3, (0) as u32);
                    lean_ctor_set(v___x_5069_, 0, v___x_5059_);
                    lean_ctor_set(v___x_5069_, 1, v___x_5067_);
                    lean_ctor_set(v___x_5069_, 2, v___x_5068_);
                    v___x_5070_ = 1usize;
                    v___x_5071_ = lean_usize_add(v_i_5047_, v___x_5070_);
                    v___x_5072_ = lean_array_uset(v_bs_x27_5054_, v_i_5047_, v___x_5069_);
                    v_i_5047_ = v___x_5071_;
                    v_bs_5048_ = v___x_5072_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___boxed(
    mut v_numDigits_5074_: *mut LeanObject,
    mut v_sz_5075_: *mut LeanObject,
    mut v_i_5076_: *mut LeanObject,
    mut v_bs_5077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5078_: usize = 0;
    let mut v_i_boxed_5079_: usize = 0;
    let mut v_res_5080_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5078_ = lean_unbox_usize(v_sz_5075_);
    lean_dec(v_sz_5075_);
    v_i_boxed_5079_ = lean_unbox_usize(v_i_5076_);
    lean_dec(v_i_5076_);
    v_res_5080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(v_numDigits_5074_, v_sz_boxed_5078_, v_i_boxed_5079_, v_bs_5077_);
    lean_dec(v_numDigits_5074_);
    return v_res_5080_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: u8 = 0;
    let mut v___x_5086_: f64 = 0.0;
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    v___x_5084_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_5085_ = 0;
    v___x_5086_ = lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2,
    );
    v___x_5087_ = lean_box(0);
    v___x_5088_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__1;
    v___x_5089_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_5089_, 0, v___x_5088_);
    lean_ctor_set(v___x_5089_, 1, v___x_5087_);
    lean_ctor_set(v___x_5089_, 2, v___x_5084_);
    lean_ctor_set_float(
        v___x_5089_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_5086_,
    );
    lean_ctor_set_float(
        v___x_5089_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_5086_,
    );
    lean_ctor_set_uint8(
        v___x_5089_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_5085_,
    );
    return v___x_5089_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    v___x_5093_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__4;
    v___x_5094_ = l_Lean_MessageData_ofFormat(v___x_5093_);
    return v___x_5094_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    v___x_5096_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__6;
    v___x_5097_ = l_Lean_stringToMessageData(v___x_5096_);
    return v___x_5097_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(
    mut v___x_5098_: u8,
    mut v_stx_5099_: *mut LeanObject,
    mut v___x_5100_: *mut LeanObject,
    mut v___x_5101_: *mut LeanObject,
    mut v___x_5102_: *mut LeanObject,
    mut v___x_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5132_: usize = 0;
    let mut v___x_5133_: usize = 0;
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDigits_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: u8 = 0;
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5168_: u8 = 0;
    let mut v_a_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5172_: u8 = 0;
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5176_: u8 = 0;
    let mut v___x_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    let mut v___x_5179_: u8 = 0;
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_filter_x3f_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_5098_ == 0 {
                    lean_dec_ref(v___x_5103_);
                    lean_dec_ref(v___x_5102_);
                    lean_dec_ref(v___x_5101_);
                    lean_dec_ref(v___x_5100_);
                    v___x_5113_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_5113_;
                } else {
                    v___x_5114_ = lean_unsigned_to_nat(1);
                    v___x_5115_ = l_Lean_Syntax_getArg(v_stx_5099_, v___x_5114_);
                    v___x_5116_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___lam__0___closed__2;
                    v___x_5117_ = l_Lean_Name_mkStr5(
                        v___x_5100_,
                        v___x_5101_,
                        v___x_5102_,
                        v___x_5103_,
                        v___x_5116_,
                    );
                    lean_inc(v___x_5115_);
                    v___x_5118_ = l_Lean_Syntax_isOfKind(v___x_5115_, v___x_5117_);
                    lean_dec(v___x_5117_);
                    if v___x_5118_ == 0 {
                        lean_dec(v___x_5115_);
                        v___x_5119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_5119_;
                    } else {
                        v___x_5120_ = lean_unsigned_to_nat(0);
                        v___x_5177_ = l_Lean_Syntax_getArg(v___x_5115_, v___x_5120_);
                        lean_dec(v___x_5115_);
                        v___x_5178_ = l_Lean_Syntax_isNone(v___x_5177_);
                        if v___x_5178_ == 0 {
                            lean_inc(v___x_5177_);
                            v___x_5179_ = l_Lean_Syntax_matchesNull(v___x_5177_, v___x_5114_);
                            if v___x_5179_ == 0 {
                                lean_dec(v___x_5177_);
                                v___x_5180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                                return v___x_5180_;
                            } else {
                                v_filter_x3f_5181_ = l_Lean_Syntax_getArg(v___x_5177_, v___x_5120_);
                                lean_dec(v___x_5177_);
                                v___x_5182_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_5182_, 0, v_filter_x3f_5181_);
                                v_filter_x3f_5140_ = v___x_5182_;
                                v___y_5141_ = v___y_5104_;
                                v___y_5142_ = v___y_5105_;
                                v___y_5143_ = v___y_5106_;
                                v___y_5144_ = v___y_5107_;
                                v___y_5145_ = v___y_5108_;
                                v___y_5146_ = v___y_5109_;
                                v___y_5147_ = v___y_5110_;
                                v___y_5148_ = v___y_5111_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_5177_);
                            v___x_5183_ = lean_box(0);
                            v_filter_x3f_5140_ = v___x_5183_;
                            v___y_5141_ = v___y_5104_;
                            v___y_5142_ = v___y_5105_;
                            v___y_5143_ = v___y_5106_;
                            v___y_5144_ = v___y_5107_;
                            v___y_5145_ = v___y_5108_;
                            v___y_5146_ = v___y_5109_;
                            v___y_5147_ = v___y_5110_;
                            v___y_5148_ = v___y_5111_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_sz_5132_ = lean_array_size(v___y_5123_);
                v___x_5133_ = 0usize;
                v___x_5134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0(v___y_5122_, v_sz_5132_, v___x_5133_, v___y_5123_);
                lean_dec(v___y_5122_);
                v___x_5135_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__2);
                v___x_5136_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__5);
                v___x_5137_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_5137_, 0, v___x_5135_);
                lean_ctor_set(v___x_5137_, 1, v___x_5136_);
                lean_ctor_set(v___x_5137_, 2, v___x_5134_);
                v___x_5138_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_5137_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, v___y_5131_);
                return v___x_5138_;
            }
            2 => {
                v___x_5149_ = l_Lean_Elab_Tactic_Grind_elabFilter(
                    v_filter_x3f_5140_,
                    v___y_5141_,
                    v___y_5142_,
                    v___y_5143_,
                    v___y_5144_,
                    v___y_5145_,
                    v___y_5146_,
                    v___y_5147_,
                    v___y_5148_,
                );
                if lean_obj_tag(v___x_5149_) == 0 {
                    v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
                    lean_inc(v_a_5150_);
                    lean_dec_ref_known(v___x_5149_, 1);
                    v___x_5151_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Filter_eval___boxed as *mut core::ffi::c_void,
                        13,
                        1,
                    );
                    lean_closure_set(v___x_5151_, 0, v_a_5150_);
                    v___x_5152_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_getSplitCandidateAnchors___boxed
                            as *mut core::ffi::c_void,
                        12,
                        1,
                    );
                    lean_closure_set(v___x_5152_, 0, v___x_5151_);
                    v___x_5153_ = l_Lean_Elab_Tactic_Grind_liftGoalM___redArg(
                        v___x_5152_,
                        v___y_5141_,
                        v___y_5142_,
                        v___y_5145_,
                        v___y_5146_,
                        v___y_5147_,
                        v___y_5148_,
                    );
                    if lean_obj_tag(v___x_5153_) == 0 {
                        v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
                        lean_inc(v_a_5154_);
                        lean_dec_ref_known(v___x_5153_, 1);
                        v_candidates_5155_ = lean_ctor_get(v_a_5154_, 0);
                        lean_inc_ref(v_candidates_5155_);
                        v_numDigits_5156_ = lean_ctor_get(v_a_5154_, 1);
                        lean_inc(v_numDigits_5156_);
                        lean_dec(v_a_5154_);
                        v___x_5157_ = lean_array_get_size(v_candidates_5155_);
                        v___x_5158_ = lean_nat_dec_eq(v___x_5157_, v___x_5120_);
                        if v___x_5158_ == 0 {
                            v___y_5122_ = v_numDigits_5156_;
                            v___y_5123_ = v_candidates_5155_;
                            v___y_5124_ = v___y_5141_;
                            v___y_5125_ = v___y_5142_;
                            v___y_5126_ = v___y_5143_;
                            v___y_5127_ = v___y_5144_;
                            v___y_5128_ = v___y_5145_;
                            v___y_5129_ = v___y_5146_;
                            v___y_5130_ = v___y_5147_;
                            v___y_5131_ = v___y_5148_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_numDigits_5156_);
                            lean_dec_ref(v_candidates_5155_);
                            v___x_5159_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___closed__7);
                            v___x_5160_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__1___redArg(v___x_5159_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
                            return v___x_5160_;
                        }
                    } else {
                        v_a_5161_ = lean_ctor_get(v___x_5153_, 0);
                        v_isSharedCheck_5168_ = (!lean_is_exclusive(v___x_5153_)) as u8;
                        if v_isSharedCheck_5168_ == 0 {
                            v___x_5163_ = v___x_5153_;
                            v_isShared_5164_ = v_isSharedCheck_5168_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5161_);
                            lean_dec(v___x_5153_);
                            v___x_5163_ = lean_box(0);
                            v_isShared_5164_ = v_isSharedCheck_5168_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_5169_ = lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5176_ = (!lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5176_ == 0 {
                        v___x_5171_ = v___x_5149_;
                        v_isShared_5172_ = v_isSharedCheck_5176_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5169_);
                        lean_dec(v___x_5149_);
                        v___x_5171_ = lean_box(0);
                        v_isShared_5172_ = v_isSharedCheck_5176_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5164_ == 0 {
                    v___x_5166_ = v___x_5163_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
                    v___x_5166_ = v_reuseFailAlloc_5167_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5166_;
            }
            5 => {
                if v_isShared_5172_ == 0 {
                    v___x_5174_ = v___x_5171_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_a_5169_);
                    v___x_5174_ = v_reuseFailAlloc_5175_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5174_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed(
    mut v___x_5184_: *mut LeanObject,
    mut v_stx_5185_: *mut LeanObject,
    mut v___x_5186_: *mut LeanObject,
    mut v___x_5187_: *mut LeanObject,
    mut v___x_5188_: *mut LeanObject,
    mut v___x_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
    mut v___y_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2300__boxed_5199_: u8 = 0;
    let mut v_res_5200_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300__boxed_5199_ = (lean_unbox(v___x_5184_) as u8);
    v_res_5200_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0(v___x_2300__boxed_5199_, v_stx_5185_, v___x_5186_, v___x_5187_, v___x_5188_, v___x_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
    lean_dec(v___y_5197_);
    lean_dec_ref(v___y_5196_);
    lean_dec(v___y_5195_);
    lean_dec_ref(v___y_5194_);
    lean_dec(v___y_5193_);
    lean_dec_ref(v___y_5192_);
    lean_dec(v___y_5191_);
    lean_dec_ref(v___y_5190_);
    lean_dec(v_stx_5185_);
    return v_res_5200_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(
    mut v_stx_5208_: *mut LeanObject,
    mut v_a_5209_: *mut LeanObject,
    mut v_a_5210_: *mut LeanObject,
    mut v_a_5211_: *mut LeanObject,
    mut v_a_5212_: *mut LeanObject,
    mut v_a_5213_: *mut LeanObject,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: u8 = 0;
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    v___x_5218_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__0;
    v___x_5219_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__1;
    v___x_5220_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___lam__0___closed__1;
    v___x_5221_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___closed__2;
    v___x_5222_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1;
    lean_inc(v_stx_5208_);
    v___x_5223_ = l_Lean_Syntax_isOfKind(v_stx_5208_, v___x_5222_);
    v___x_5224_ = lean_box((v___x_5223_) as usize);
    v___y_5225_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___lam__0___boxed as *mut core::ffi::c_void, 15, 6);
    lean_closure_set(v___y_5225_, 0, v___x_5224_);
    lean_closure_set(v___y_5225_, 1, v_stx_5208_);
    lean_closure_set(v___y_5225_, 2, v___x_5218_);
    lean_closure_set(v___y_5225_, 3, v___x_5219_);
    lean_closure_set(v___y_5225_, 4, v___x_5220_);
    lean_closure_set(v___y_5225_, 5, v___x_5221_);
    v___x_5226_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___y_5225_,
        v_a_5209_,
        v_a_5210_,
        v_a_5211_,
        v_a_5212_,
        v_a_5213_,
        v_a_5214_,
        v_a_5215_,
        v_a_5216_,
    );
    return v___x_5226_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed(
    mut v_stx_5227_: *mut LeanObject,
    mut v_a_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
    mut v_a_5230_: *mut LeanObject,
    mut v_a_5231_: *mut LeanObject,
    mut v_a_5232_: *mut LeanObject,
    mut v_a_5233_: *mut LeanObject,
    mut v_a_5234_: *mut LeanObject,
    mut v_a_5235_: *mut LeanObject,
    mut v_a_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_res_5237_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases(
            v_stx_5227_,
            v_a_5228_,
            v_a_5229_,
            v_a_5230_,
            v_a_5231_,
            v_a_5232_,
            v_a_5233_,
            v_a_5234_,
            v_a_5235_,
        );
    lean_dec(v_a_5235_);
    lean_dec_ref(v_a_5234_);
    lean_dec(v_a_5233_);
    lean_dec_ref(v_a_5232_);
    lean_dec(v_a_5231_);
    lean_dec_ref(v_a_5230_);
    lean_dec(v_a_5229_);
    lean_dec_ref(v_a_5228_);
    return v_res_5237_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1()
-> *mut LeanObject {
    let mut v___x_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    v___x_5243_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_5244_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___closed__1;
    v___x_5245_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___closed__1;
    v___x_5246_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5247_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5243_,
        v___x_5244_,
        v___x_5245_,
        v___x_5246_,
    );
    return v___x_5247_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1___boxed(
    mut v_a_5248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5249_: *mut LeanObject = core::ptr::null_mut();
    v_res_5249_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
    return v_res_5249_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_a_5250_: u64,
    mut v_x_5251_: *mut LeanObject,
) -> u8 {
    let mut v___x_5252_: u8 = 0;
    let mut v_key_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u64 = 0;
    let mut v___x_5256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5251_) == 0 {
                    v___x_5252_ = 0;
                    return v___x_5252_;
                } else {
                    v_key_5253_ = lean_ctor_get(v_x_5251_, 0);
                    v_tail_5254_ = lean_ctor_get(v_x_5251_, 2);
                    v___x_5255_ = lean_unbox_uint64(v_key_5253_);
                    v___x_5256_ = lean_uint64_dec_eq(v___x_5255_, v_a_5250_);
                    if v___x_5256_ == 0 {
                        v_x_5251_ = v_tail_5254_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5256_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_5258_: *mut LeanObject,
    mut v_x_5259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5260_: u64 = 0;
    let mut v_res_5261_: u8 = 0;
    let mut v_r_5262_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5260_ = lean_unbox_uint64(v_a_5258_);
    lean_dec_ref(v_a_5258_);
    v_res_5261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_boxed_5260_, v_x_5259_);
    lean_dec(v_x_5259_);
    v_r_5262_ = lean_box((v_res_5261_) as usize);
    return v_r_5262_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(
    mut v_m_5263_: *mut LeanObject,
    mut v_a_5264_: u64,
) -> u8 {
    let mut v_buckets_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: u64 = 0;
    let mut v___x_5268_: u64 = 0;
    let mut v_fold_5269_: u64 = 0;
    let mut v___x_5270_: u64 = 0;
    let mut v___x_5271_: u64 = 0;
    let mut v___x_5272_: u64 = 0;
    let mut v___x_5273_: usize = 0;
    let mut v___x_5274_: usize = 0;
    let mut v___x_5275_: usize = 0;
    let mut v___x_5276_: usize = 0;
    let mut v___x_5277_: usize = 0;
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: u8 = 0;
    v_buckets_5265_ = lean_ctor_get(v_m_5263_, 1);
    v___x_5266_ = lean_array_get_size(v_buckets_5265_);
    v___x_5267_ = 32u64;
    v___x_5268_ = lean_uint64_shift_right(v_a_5264_, v___x_5267_);
    v_fold_5269_ = lean_uint64_xor(v_a_5264_, v___x_5268_);
    v___x_5270_ = 16u64;
    v___x_5271_ = lean_uint64_shift_right(v_fold_5269_, v___x_5270_);
    v___x_5272_ = lean_uint64_xor(v_fold_5269_, v___x_5271_);
    v___x_5273_ = lean_uint64_to_usize(v___x_5272_);
    v___x_5274_ = lean_usize_of_nat(v___x_5266_);
    v___x_5275_ = 1usize;
    v___x_5276_ = lean_usize_sub(v___x_5274_, v___x_5275_);
    v___x_5277_ = lean_usize_land(v___x_5273_, v___x_5276_);
    v___x_5278_ = lean_array_uget_borrowed(v_buckets_5265_, v___x_5277_);
    v___x_5279_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_5264_, v___x_5278_);
    return v___x_5279_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_m_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5282_: u64 = 0;
    let mut v_res_5283_: u8 = 0;
    let mut v_r_5284_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5282_ = lean_unbox_uint64(v_a_5281_);
    lean_dec_ref(v_a_5281_);
    v_res_5283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_m_5280_, v_a_boxed_5282_);
    lean_dec_ref(v_m_5280_);
    v_r_5284_ = lean_box((v_res_5283_) as usize);
    return v_r_5284_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(
    mut v_x_5285_: *mut LeanObject,
    mut v_x_5286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: u64 = 0;
    let mut v___x_5295_: u64 = 0;
    let mut v___x_5296_: u64 = 0;
    let mut v___x_5297_: u64 = 0;
    let mut v_fold_5298_: u64 = 0;
    let mut v___x_5299_: u64 = 0;
    let mut v___x_5300_: u64 = 0;
    let mut v___x_5301_: u64 = 0;
    let mut v___x_5302_: usize = 0;
    let mut v___x_5303_: usize = 0;
    let mut v___x_5304_: usize = 0;
    let mut v___x_5305_: usize = 0;
    let mut v___x_5306_: usize = 0;
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5286_) == 0 {
                    return v_x_5285_;
                } else {
                    v_key_5287_ = lean_ctor_get(v_x_5286_, 0);
                    v_value_5288_ = lean_ctor_get(v_x_5286_, 1);
                    v_tail_5289_ = lean_ctor_get(v_x_5286_, 2);
                    v_isSharedCheck_5313_ = (!lean_is_exclusive(v_x_5286_)) as u8;
                    if v_isSharedCheck_5313_ == 0 {
                        v___x_5291_ = v_x_5286_;
                        v_isShared_5292_ = v_isSharedCheck_5313_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5289_);
                        lean_inc(v_value_5288_);
                        lean_inc(v_key_5287_);
                        lean_dec(v_x_5286_);
                        v___x_5291_ = lean_box(0);
                        v_isShared_5292_ = v_isSharedCheck_5313_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5293_ = lean_array_get_size(v_x_5285_);
                v___x_5294_ = 32u64;
                v___x_5295_ = lean_unbox_uint64(v_key_5287_);
                v___x_5296_ = lean_uint64_shift_right(v___x_5295_, v___x_5294_);
                v___x_5297_ = lean_unbox_uint64(v_key_5287_);
                v_fold_5298_ = lean_uint64_xor(v___x_5297_, v___x_5296_);
                v___x_5299_ = 16u64;
                v___x_5300_ = lean_uint64_shift_right(v_fold_5298_, v___x_5299_);
                v___x_5301_ = lean_uint64_xor(v_fold_5298_, v___x_5300_);
                v___x_5302_ = lean_uint64_to_usize(v___x_5301_);
                v___x_5303_ = lean_usize_of_nat(v___x_5293_);
                v___x_5304_ = 1usize;
                v___x_5305_ = lean_usize_sub(v___x_5303_, v___x_5304_);
                v___x_5306_ = lean_usize_land(v___x_5302_, v___x_5305_);
                v___x_5307_ = lean_array_uget_borrowed(v_x_5285_, v___x_5306_);
                lean_inc(v___x_5307_);
                if v_isShared_5292_ == 0 {
                    lean_ctor_set(v___x_5291_, 2, v___x_5307_);
                    v___x_5309_ = v___x_5291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_key_5287_);
                    lean_ctor_set(v_reuseFailAlloc_5312_, 1, v_value_5288_);
                    lean_ctor_set(v_reuseFailAlloc_5312_, 2, v___x_5307_);
                    v___x_5309_ = v_reuseFailAlloc_5312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5310_ = lean_array_uset(v_x_5285_, v___x_5306_, v___x_5309_);
                v_x_5285_ = v___x_5310_;
                v_x_5286_ = v_tail_5289_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_i_5314_: *mut LeanObject,
    mut v_source_5315_: *mut LeanObject,
    mut v_target_5316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: u8 = 0;
    let mut v_es_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5317_ = lean_array_get_size(v_source_5315_);
                v___x_5318_ = lean_nat_dec_lt(v_i_5314_, v___x_5317_);
                if v___x_5318_ == 0 {
                    lean_dec_ref(v_source_5315_);
                    lean_dec(v_i_5314_);
                    return v_target_5316_;
                } else {
                    v_es_5319_ = lean_array_fget(v_source_5315_, v_i_5314_);
                    v___x_5320_ = lean_box(0);
                    v_source_5321_ = lean_array_fset(v_source_5315_, v_i_5314_, v___x_5320_);
                    v_target_5322_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(v_target_5316_, v_es_5319_);
                    v___x_5323_ = lean_unsigned_to_nat(1);
                    v___x_5324_ = lean_nat_add(v_i_5314_, v___x_5323_);
                    lean_dec(v_i_5314_);
                    v_i_5314_ = v___x_5324_;
                    v_source_5315_ = v_source_5321_;
                    v_target_5316_ = v_target_5322_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_data_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut LeanObject = core::ptr::null_mut();
    v___x_5327_ = lean_array_get_size(v_data_5326_);
    v___x_5328_ = lean_unsigned_to_nat(2);
    v_nbuckets_5329_ = lean_nat_mul(v___x_5327_, v___x_5328_);
    v___x_5330_ = lean_unsigned_to_nat(0);
    v___x_5331_ = lean_box(0);
    v___x_5332_ = lean_mk_array(v_nbuckets_5329_, v___x_5331_);
    v___x_5333_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v___x_5330_, v_data_5326_, v___x_5332_);
    return v___x_5333_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(
    mut v_m_5334_: *mut LeanObject,
    mut v_a_5335_: u64,
    mut v_b_5336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: u64 = 0;
    let mut v___x_5341_: u64 = 0;
    let mut v_fold_5342_: u64 = 0;
    let mut v___x_5343_: u64 = 0;
    let mut v___x_5344_: u64 = 0;
    let mut v___x_5345_: u64 = 0;
    let mut v___x_5346_: usize = 0;
    let mut v___x_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: usize = 0;
    let mut v___x_5350_: usize = 0;
    let mut v_bkt_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v___x_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v_val_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_unused_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5337_ = lean_ctor_get(v_m_5334_, 0);
                v_buckets_5338_ = lean_ctor_get(v_m_5334_, 1);
                v___x_5339_ = lean_array_get_size(v_buckets_5338_);
                v___x_5340_ = 32u64;
                v___x_5341_ = lean_uint64_shift_right(v_a_5335_, v___x_5340_);
                v_fold_5342_ = lean_uint64_xor(v_a_5335_, v___x_5341_);
                v___x_5343_ = 16u64;
                v___x_5344_ = lean_uint64_shift_right(v_fold_5342_, v___x_5343_);
                v___x_5345_ = lean_uint64_xor(v_fold_5342_, v___x_5344_);
                v___x_5346_ = lean_uint64_to_usize(v___x_5345_);
                v___x_5347_ = lean_usize_of_nat(v___x_5339_);
                v___x_5348_ = 1usize;
                v___x_5349_ = lean_usize_sub(v___x_5347_, v___x_5348_);
                v___x_5350_ = lean_usize_land(v___x_5346_, v___x_5349_);
                v_bkt_5351_ = lean_array_uget_borrowed(v_buckets_5338_, v___x_5350_);
                v___x_5352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_5335_, v_bkt_5351_);
                if v___x_5352_ == 0 {
                    lean_inc_ref(v_buckets_5338_);
                    lean_inc(v_size_5337_);
                    v_isSharedCheck_5374_ = (!lean_is_exclusive(v_m_5334_)) as u8;
                    if v_isSharedCheck_5374_ == 0 {
                        v_unused_5375_ = lean_ctor_get(v_m_5334_, 1);
                        lean_dec(v_unused_5375_);
                        v_unused_5376_ = lean_ctor_get(v_m_5334_, 0);
                        lean_dec(v_unused_5376_);
                        v___x_5354_ = v_m_5334_;
                        v_isShared_5355_ = v_isSharedCheck_5374_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5334_);
                        v___x_5354_ = lean_box(0);
                        v_isShared_5355_ = v_isSharedCheck_5374_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5336_);
                    return v_m_5334_;
                }
            }
            1 => {
                v___x_5356_ = lean_unsigned_to_nat(1);
                v_size_x27_5357_ = lean_nat_add(v_size_5337_, v___x_5356_);
                lean_dec(v_size_5337_);
                v___x_5358_ = lean_box_uint64(v_a_5335_);
                lean_inc(v_bkt_5351_);
                v___x_5359_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5359_, 0, v___x_5358_);
                lean_ctor_set(v___x_5359_, 1, v_b_5336_);
                lean_ctor_set(v___x_5359_, 2, v_bkt_5351_);
                v_buckets_x27_5360_ = lean_array_uset(v_buckets_5338_, v___x_5350_, v___x_5359_);
                v___x_5361_ = lean_unsigned_to_nat(4);
                v___x_5362_ = lean_nat_mul(v_size_x27_5357_, v___x_5361_);
                v___x_5363_ = lean_unsigned_to_nat(3);
                v___x_5364_ = lean_nat_div(v___x_5362_, v___x_5363_);
                lean_dec(v___x_5362_);
                v___x_5365_ = lean_array_get_size(v_buckets_x27_5360_);
                v___x_5366_ = lean_nat_dec_le(v___x_5364_, v___x_5365_);
                lean_dec(v___x_5364_);
                if v___x_5366_ == 0 {
                    v_val_5367_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(v_buckets_x27_5360_);
                    if v_isShared_5355_ == 0 {
                        lean_ctor_set(v___x_5354_, 1, v_val_5367_);
                        lean_ctor_set(v___x_5354_, 0, v_size_x27_5357_);
                        v___x_5369_ = v___x_5354_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_size_x27_5357_);
                        lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_val_5367_);
                        v___x_5369_ = v_reuseFailAlloc_5370_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5355_ == 0 {
                        lean_ctor_set(v___x_5354_, 1, v_buckets_x27_5360_);
                        lean_ctor_set(v___x_5354_, 0, v_size_x27_5357_);
                        v___x_5372_ = v___x_5354_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_size_x27_5357_);
                        lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_buckets_x27_5360_);
                        v___x_5372_ = v_reuseFailAlloc_5373_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5369_;
            }
            3 => {
                return v___x_5372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_m_5377_: *mut LeanObject,
    mut v_a_5378_: *mut LeanObject,
    mut v_b_5379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5380_: u64 = 0;
    let mut v_res_5381_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5380_ = lean_unbox_uint64(v_a_5378_);
    lean_dec_ref(v_a_5378_);
    v_res_5381_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_m_5377_, v_a_boxed_5380_, v_b_5379_);
    return v_res_5381_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    v___x_5382_ = lean_box(0);
    v___x_5383_ = lean_unsigned_to_nat(16);
    v___x_5384_ = lean_mk_array(v___x_5383_, v___x_5382_);
    return v___x_5384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_5387_: *mut LeanObject = core::ptr::null_mut();
    v___x_5385_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__0);
    v___x_5386_ = lean_unsigned_to_nat(0);
    v_found_5387_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_found_5387_, 0, v___x_5386_);
    lean_ctor_set(v_found_5387_, 1, v___x_5385_);
    return v_found_5387_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v_found_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    v_found_5388_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__1);
    v___x_5389_ = lean_box(0);
    v___x_5390_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5390_, 0, v___x_5389_);
    lean_ctor_set(v___x_5390_, 1, v_found_5388_);
    return v___x_5390_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(
    mut v_shift_5391_: *mut LeanObject,
    mut v_numDigits_5392_: *mut LeanObject,
    mut v_es_5393_: *mut LeanObject,
    mut v_as_5394_: *mut LeanObject,
    mut v_sz_5395_: usize,
    mut v_i_5396_: usize,
    mut v_b_5397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5398_: u8 = 0;
    let mut v_snd_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5402_: u8 = 0;
    let mut v_a_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchor_5404_: u64 = 0;
    let mut v___x_5405_: u64 = 0;
    let mut v___x_5406_: u64 = 0;
    let mut v___x_5407_: u8 = 0;
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: usize = 0;
    let mut v___x_5414_: usize = 0;
    let mut v_reuseFailAlloc_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5424_: u8 = 0;
    let mut v_unused_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5398_ = lean_usize_dec_lt(v_i_5396_, v_sz_5395_);
                if v___x_5398_ == 0 {
                    return v_b_5397_;
                } else {
                    v_snd_5399_ = lean_ctor_get(v_b_5397_, 1);
                    v_isSharedCheck_5424_ = (!lean_is_exclusive(v_b_5397_)) as u8;
                    if v_isSharedCheck_5424_ == 0 {
                        v_unused_5425_ = lean_ctor_get(v_b_5397_, 0);
                        lean_dec(v_unused_5425_);
                        v___x_5401_ = v_b_5397_;
                        v_isShared_5402_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5399_);
                        lean_dec(v_b_5397_);
                        v___x_5401_ = lean_box(0);
                        v_isShared_5402_ = v_isSharedCheck_5424_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5403_ = lean_array_uget_borrowed(v_as_5394_, v_i_5396_);
                v_anchor_5404_ = lean_ctor_get_uint64(
                    v_a_5403_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_5405_ = lean_uint64_of_nat(v_shift_5391_);
                v___x_5406_ = lean_uint64_shift_right(v_anchor_5404_, v___x_5405_);
                v___x_5407_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_snd_5399_, v___x_5406_);
                if v___x_5407_ == 0 {
                    v___x_5408_ = lean_box(0);
                    v___x_5409_ = lean_box(0);
                    v___x_5410_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_snd_5399_, v___x_5406_, v___x_5409_);
                    if v_isShared_5402_ == 0 {
                        lean_ctor_set(v___x_5401_, 1, v___x_5410_);
                        lean_ctor_set(v___x_5401_, 0, v___x_5408_);
                        v___x_5412_ = v___x_5401_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5408_);
                        lean_ctor_set(v_reuseFailAlloc_5416_, 1, v___x_5410_);
                        v___x_5412_ = v_reuseFailAlloc_5416_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5417_ = lean_unsigned_to_nat(1);
                    v___x_5418_ = lean_nat_add(v_numDigits_5392_, v___x_5417_);
                    v___x_5419_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_5393_, v___x_5418_);
                    lean_dec(v___x_5418_);
                    v___x_5420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5420_, 0, v___x_5419_);
                    if v_isShared_5402_ == 0 {
                        lean_ctor_set(v___x_5401_, 0, v___x_5420_);
                        v___x_5422_ = v___x_5401_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
                        lean_ctor_set(v_reuseFailAlloc_5423_, 1, v_snd_5399_);
                        v___x_5422_ = v_reuseFailAlloc_5423_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5413_ = 1usize;
                v___x_5414_ = lean_usize_add(v_i_5396_, v___x_5413_);
                v_i_5396_ = v___x_5414_;
                v_b_5397_ = v___x_5412_;
                state = 0;
                continue;
            }
            3 => {
                return v___x_5422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(
    mut v_es_5426_: *mut LeanObject,
    mut v_numDigits_5427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    v___x_5428_ = lean_unsigned_to_nat(4);
    v___x_5429_ = lean_nat_mul(v___x_5428_, v_numDigits_5427_);
    v___x_5430_ = lean_unsigned_to_nat(64);
    v___x_5431_ = lean_nat_dec_lt(v___x_5429_, v___x_5430_);
    if v___x_5431_ == 0 {
        lean_dec(v___x_5429_);
        lean_inc(v_numDigits_5427_);
        return v_numDigits_5427_;
    } else {
        let mut v_shift_5432_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_5434_: usize = 0;
        let mut v___x_5435_: usize = 0;
        let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_5437_: *mut LeanObject = core::ptr::null_mut();
        v_shift_5432_ = lean_nat_sub(v___x_5430_, v___x_5429_);
        lean_dec(v___x_5429_);
        v___x_5433_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___closed__2);
        v_sz_5434_ = lean_array_size(v_es_5426_);
        v___x_5435_ = 0usize;
        v___x_5436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(v_shift_5432_, v_numDigits_5427_, v_es_5426_, v_es_5426_, v_sz_5434_, v___x_5435_, v___x_5433_);
        lean_dec(v_shift_5432_);
        v_fst_5437_ = lean_ctor_get(v___x_5436_, 0);
        lean_inc(v_fst_5437_);
        lean_dec_ref(v___x_5436_);
        if lean_obj_tag(v_fst_5437_) == 0 {
            lean_inc(v_numDigits_5427_);
            return v_numDigits_5427_;
        } else {
            let mut v_val_5438_: *mut LeanObject = core::ptr::null_mut();
            v_val_5438_ = lean_ctor_get(v_fst_5437_, 0);
            lean_inc(v_val_5438_);
            lean_dec_ref_known(v_fst_5437_, 1);
            return v_val_5438_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0___boxed(
    mut v_es_5439_: *mut LeanObject,
    mut v_numDigits_5440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5441_: *mut LeanObject = core::ptr::null_mut();
    v_res_5441_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_5439_, v_numDigits_5440_);
    lean_dec(v_numDigits_5440_);
    lean_dec_ref(v_es_5439_);
    return v_res_5441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3___boxed(
    mut v_shift_5442_: *mut LeanObject,
    mut v_numDigits_5443_: *mut LeanObject,
    mut v_es_5444_: *mut LeanObject,
    mut v_as_5445_: *mut LeanObject,
    mut v_sz_5446_: *mut LeanObject,
    mut v_i_5447_: *mut LeanObject,
    mut v_b_5448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5449_: usize = 0;
    let mut v_i_boxed_5450_: usize = 0;
    let mut v_res_5451_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5449_ = lean_unbox_usize(v_sz_5446_);
    lean_dec(v_sz_5446_);
    v_i_boxed_5450_ = lean_unbox_usize(v_i_5447_);
    lean_dec(v_i_5447_);
    v_res_5451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__3(v_shift_5442_, v_numDigits_5443_, v_es_5444_, v_as_5445_, v_sz_boxed_5449_, v_i_boxed_5450_, v_b_5448_);
    lean_dec_ref(v_as_5445_);
    lean_dec_ref(v_es_5444_);
    lean_dec(v_numDigits_5443_);
    lean_dec(v_shift_5442_);
    return v_res_5451_;
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(
    mut v_es_5452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    v___x_5453_ = lean_unsigned_to_nat(4);
    v___x_5454_ = l___private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0(v_es_5452_, v___x_5453_);
    return v___x_5454_;
}
pub unsafe fn l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0___boxed(
    mut v_es_5455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5456_: *mut LeanObject = core::ptr::null_mut();
    v_res_5456_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(v_es_5455_);
    lean_dec_ref(v_es_5455_);
    return v_res_5456_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(
    mut v___x_5460_: *mut LeanObject,
    mut v_sz_5461_: usize,
    mut v_i_5462_: usize,
    mut v_bs_5463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5464_: u8 = 0;
    let mut v_v_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchor_5467_: u64 = 0;
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: f64 = 0.0;
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: usize = 0;
    let mut v___x_5486_: usize = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5464_ = lean_usize_dec_lt(v_i_5462_, v_sz_5461_);
                if v___x_5464_ == 0 {
                    return v_bs_5463_;
                } else {
                    v_v_5465_ = lean_array_uget_borrowed(v_bs_5463_, v_i_5462_);
                    v_e_5466_ = lean_ctor_get(v_v_5465_, 0);
                    lean_inc_ref(v_e_5466_);
                    v_anchor_5467_ = lean_ctor_get_uint64(
                        v_v_5465_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_5468_ = lean_unsigned_to_nat(0);
                    v_bs_x27_5469_ = lean_array_uset(v_bs_5463_, v_i_5462_, v___x_5468_);
                    v___x_5470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___closed__1;
                    v___x_5471_ = lean_box(0);
                    v___x_5472_ = lean_float_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2,
                    );
                    v___x_5473_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
                    v___x_5474_ = lean_alloc_ctor(0, 3, (17) as u32);
                    lean_ctor_set(v___x_5474_, 0, v___x_5470_);
                    lean_ctor_set(v___x_5474_, 1, v___x_5471_);
                    lean_ctor_set(v___x_5474_, 2, v___x_5473_);
                    lean_ctor_set_float(
                        v___x_5474_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v___x_5472_,
                    );
                    lean_ctor_set_float(
                        v___x_5474_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        v___x_5472_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5474_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                        v___x_5464_,
                    );
                    v___x_5475_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__3);
                    v___x_5476_ = l_Lean_Meta_Grind_anchorToString(v___x_5460_, v_anchor_5467_);
                    v___x_5477_ = l_Lean_stringToMessageData(v___x_5476_);
                    v___x_5478_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5478_, 0, v___x_5475_);
                    lean_ctor_set(v___x_5478_, 1, v___x_5477_);
                    v___x_5479_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases_spec__0___closed__5);
                    v___x_5480_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5480_, 0, v___x_5478_);
                    lean_ctor_set(v___x_5480_, 1, v___x_5479_);
                    v___x_5481_ = l_Lean_MessageData_ofExpr(v_e_5466_);
                    v___x_5482_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5482_, 0, v___x_5480_);
                    lean_ctor_set(v___x_5482_, 1, v___x_5481_);
                    v___x_5483_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_ppEqcs_x3f_spec__5___redArg___closed__0;
                    v___x_5484_ = lean_alloc_ctor(9, 3, (0) as u32);
                    lean_ctor_set(v___x_5484_, 0, v___x_5474_);
                    lean_ctor_set(v___x_5484_, 1, v___x_5482_);
                    lean_ctor_set(v___x_5484_, 2, v___x_5483_);
                    v___x_5485_ = 1usize;
                    v___x_5486_ = lean_usize_add(v_i_5462_, v___x_5485_);
                    v___x_5487_ = lean_array_uset(v_bs_x27_5469_, v_i_5462_, v___x_5484_);
                    v_i_5462_ = v___x_5486_;
                    v_bs_5463_ = v___x_5487_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1___boxed(
    mut v___x_5489_: *mut LeanObject,
    mut v_sz_5490_: *mut LeanObject,
    mut v_i_5491_: *mut LeanObject,
    mut v_bs_5492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5493_: usize = 0;
    let mut v_i_boxed_5494_: usize = 0;
    let mut v_res_5495_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5493_ = lean_unbox_usize(v_sz_5490_);
    lean_dec(v_sz_5490_);
    v_i_boxed_5494_ = lean_unbox_usize(v_i_5491_);
    lean_dec(v_i_5491_);
    v_res_5495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(v___x_5489_, v_sz_boxed_5493_, v_i_boxed_5494_, v_bs_5492_);
    lean_dec(v___x_5489_);
    return v_res_5495_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: u8 = 0;
    let mut v___x_5501_: f64 = 0.0;
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    v___x_5499_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_5500_ = 0;
    v___x_5501_ = lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Grind_showState___redArg___closed__2,
    );
    v___x_5502_ = lean_box(0);
    v___x_5503_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__1;
    v___x_5504_ = lean_alloc_ctor(0, 3, (17) as u32);
    lean_ctor_set(v___x_5504_, 0, v___x_5503_);
    lean_ctor_set(v___x_5504_, 1, v___x_5502_);
    lean_ctor_set(v___x_5504_, 2, v___x_5499_);
    lean_ctor_set_float(
        v___x_5504_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_5501_,
    );
    lean_ctor_set_float(
        v___x_5504_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        v___x_5501_,
    );
    lean_ctor_set_uint8(
        v___x_5504_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
        v___x_5500_,
    );
    return v___x_5504_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    v___x_5508_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__4;
    v___x_5509_ = l_Lean_MessageData_ofFormat(v___x_5508_);
    return v___x_5509_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(
    mut v___y_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
    mut v___y_5513_: *mut LeanObject,
    mut v___y_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5525_: usize = 0;
    let mut v___x_5526_: usize = 0;
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut v_a_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5519_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(
                    v___y_5511_,
                    v___y_5514_,
                    v___y_5515_,
                    v___y_5516_,
                    v___y_5517_,
                );
                if lean_obj_tag(v___x_5519_) == 0 {
                    v_a_5520_ = lean_ctor_get(v___x_5519_, 0);
                    lean_inc(v_a_5520_);
                    lean_dec_ref_known(v___x_5519_, 1);
                    v___x_5521_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_getLocalTheoremAnchors___boxed as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___x_5521_, 0, v_a_5520_);
                    v___x_5522_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(
                        v___x_5521_,
                        v___y_5510_,
                        v___y_5511_,
                        v___y_5514_,
                        v___y_5515_,
                        v___y_5516_,
                        v___y_5517_,
                    );
                    if lean_obj_tag(v___x_5522_) == 0 {
                        v_a_5523_ = lean_ctor_get(v___x_5522_, 0);
                        lean_inc(v_a_5523_);
                        lean_dec_ref_known(v___x_5522_, 1);
                        v___x_5524_ = l_Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0(v_a_5523_);
                        v_sz_5525_ = lean_array_size(v_a_5523_);
                        v___x_5526_ = 0usize;
                        v___x_5527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__1(v___x_5524_, v_sz_5525_, v___x_5526_, v_a_5523_);
                        lean_dec(v___x_5524_);
                        v___x_5528_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__2);
                        v___x_5529_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5_once), _init_l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___closed__5);
                        v___x_5530_ = lean_alloc_ctor(9, 3, (0) as u32);
                        lean_ctor_set(v___x_5530_, 0, v___x_5528_);
                        lean_ctor_set(v___x_5530_, 1, v___x_5529_);
                        lean_ctor_set(v___x_5530_, 2, v___x_5527_);
                        v___x_5531_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_5530_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_);
                        return v___x_5531_;
                    } else {
                        v_a_5532_ = lean_ctor_get(v___x_5522_, 0);
                        v_isSharedCheck_5539_ = (!lean_is_exclusive(v___x_5522_)) as u8;
                        if v_isSharedCheck_5539_ == 0 {
                            v___x_5534_ = v___x_5522_;
                            v_isShared_5535_ = v_isSharedCheck_5539_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5532_);
                            lean_dec(v___x_5522_);
                            v___x_5534_ = lean_box(0);
                            v_isShared_5535_ = v_isSharedCheck_5539_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_5540_ = lean_ctor_get(v___x_5519_, 0);
                    v_isSharedCheck_5547_ = (!lean_is_exclusive(v___x_5519_)) as u8;
                    if v_isSharedCheck_5547_ == 0 {
                        v___x_5542_ = v___x_5519_;
                        v_isShared_5543_ = v_isSharedCheck_5547_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5540_);
                        lean_dec(v___x_5519_);
                        v___x_5542_ = lean_box(0);
                        v_isShared_5543_ = v_isSharedCheck_5547_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5535_ == 0 {
                    v___x_5537_ = v___x_5534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
                    v___x_5537_ = v_reuseFailAlloc_5538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5537_;
            }
            3 => {
                if v_isShared_5543_ == 0 {
                    v___x_5545_ = v___x_5542_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
                    v___x_5545_ = v_reuseFailAlloc_5546_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5545_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0___boxed(
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
    mut v___y_5553_: *mut LeanObject,
    mut v___y_5554_: *mut LeanObject,
    mut v___y_5555_: *mut LeanObject,
    mut v___y_5556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5557_: *mut LeanObject = core::ptr::null_mut();
    v_res_5557_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___lam__0(v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
    lean_dec(v___y_5555_);
    lean_dec_ref(v___y_5554_);
    lean_dec(v___y_5553_);
    lean_dec_ref(v___y_5552_);
    lean_dec(v___y_5551_);
    lean_dec_ref(v___y_5550_);
    lean_dec(v___y_5549_);
    lean_dec_ref(v___y_5548_);
    return v_res_5557_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(
    mut v_a_5559_: *mut LeanObject,
    mut v_a_5560_: *mut LeanObject,
    mut v_a_5561_: *mut LeanObject,
    mut v_a_5562_: *mut LeanObject,
    mut v_a_5563_: *mut LeanObject,
    mut v_a_5564_: *mut LeanObject,
    mut v_a_5565_: *mut LeanObject,
    mut v_a_5566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    v___f_5568_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___closed__0;
    v___x_5569_ = l_Lean_Elab_Tactic_Grind_withMainContext___redArg(
        v___f_5568_,
        v_a_5559_,
        v_a_5560_,
        v_a_5561_,
        v_a_5562_,
        v_a_5563_,
        v_a_5564_,
        v_a_5565_,
        v_a_5566_,
    );
    return v___x_5569_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg___boxed(
    mut v_a_5570_: *mut LeanObject,
    mut v_a_5571_: *mut LeanObject,
    mut v_a_5572_: *mut LeanObject,
    mut v_a_5573_: *mut LeanObject,
    mut v_a_5574_: *mut LeanObject,
    mut v_a_5575_: *mut LeanObject,
    mut v_a_5576_: *mut LeanObject,
    mut v_a_5577_: *mut LeanObject,
    mut v_a_5578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5579_: *mut LeanObject = core::ptr::null_mut();
    v_res_5579_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(v_a_5570_, v_a_5571_, v_a_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_);
    lean_dec(v_a_5577_);
    lean_dec_ref(v_a_5576_);
    lean_dec(v_a_5575_);
    lean_dec_ref(v_a_5574_);
    lean_dec(v_a_5573_);
    lean_dec_ref(v_a_5572_);
    lean_dec(v_a_5571_);
    lean_dec_ref(v_a_5570_);
    return v_res_5579_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(
    mut v_x_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
    mut v_a_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
    mut v_a_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    v___x_5590_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___redArg(v_a_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_, v_a_5588_);
    return v___x_5590_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed(
    mut v_x_5591_: *mut LeanObject,
    mut v_a_5592_: *mut LeanObject,
    mut v_a_5593_: *mut LeanObject,
    mut v_a_5594_: *mut LeanObject,
    mut v_a_5595_: *mut LeanObject,
    mut v_a_5596_: *mut LeanObject,
    mut v_a_5597_: *mut LeanObject,
    mut v_a_5598_: *mut LeanObject,
    mut v_a_5599_: *mut LeanObject,
    mut v_a_5600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5601_: *mut LeanObject = core::ptr::null_mut();
    v_res_5601_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms(
            v_x_5591_, v_a_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_,
            v_a_5599_,
        );
    lean_dec(v_a_5599_);
    lean_dec_ref(v_a_5598_);
    lean_dec(v_a_5597_);
    lean_dec_ref(v_a_5596_);
    lean_dec(v_a_5595_);
    lean_dec_ref(v_a_5594_);
    lean_dec(v_a_5593_);
    lean_dec_ref(v_a_5592_);
    lean_dec(v_x_5591_);
    return v_res_5601_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5602_: *mut LeanObject,
    mut v_m_5603_: *mut LeanObject,
    mut v_a_5604_: u64,
) -> u8 {
    let mut v___x_5605_: u8 = 0;
    v___x_5605_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___redArg(v_m_5603_, v_a_5604_);
    return v___x_5605_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5606_: *mut LeanObject,
    mut v_m_5607_: *mut LeanObject,
    mut v_a_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5609_: u64 = 0;
    let mut v_res_5610_: u8 = 0;
    let mut v_r_5611_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5609_ = lean_unbox_uint64(v_a_5608_);
    lean_dec_ref(v_a_5608_);
    v_res_5610_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1(v_00_u03b2_5606_, v_m_5607_, v_a_boxed_5609_);
    lean_dec_ref(v_m_5607_);
    v_r_5611_ = lean_box((v_res_5610_) as usize);
    return v_r_5611_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5612_: *mut LeanObject,
    mut v_m_5613_: *mut LeanObject,
    mut v_a_5614_: u64,
    mut v_b_5615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    v___x_5616_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___redArg(v_m_5613_, v_a_5614_, v_b_5615_);
    return v___x_5616_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5617_: *mut LeanObject,
    mut v_m_5618_: *mut LeanObject,
    mut v_a_5619_: *mut LeanObject,
    mut v_b_5620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5621_: u64 = 0;
    let mut v_res_5622_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5621_ = lean_unbox_uint64(v_a_5619_);
    lean_dec_ref(v_a_5619_);
    v_res_5622_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2(v_00_u03b2_5617_, v_m_5618_, v_a_boxed_5621_, v_b_5620_);
    return v_res_5622_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5623_: *mut LeanObject,
    mut v_a_5624_: u64,
    mut v_x_5625_: *mut LeanObject,
) -> u8 {
    let mut v___x_5626_: u8 = 0;
    v___x_5626_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___redArg(v_a_5624_, v_x_5625_);
    return v___x_5626_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_5627_: *mut LeanObject,
    mut v_a_5628_: *mut LeanObject,
    mut v_x_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_5630_: u64 = 0;
    let mut v_res_5631_: u8 = 0;
    let mut v_r_5632_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_5630_ = lean_unbox_uint64(v_a_5628_);
    lean_dec_ref(v_a_5628_);
    v_res_5631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_5627_, v_a_boxed_5630_, v_x_5629_);
    lean_dec(v_x_5629_);
    v_r_5632_ = lean_box((v_res_5631_) as usize);
    return v_r_5632_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_5633_: *mut LeanObject,
    mut v_data_5634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    v___x_5635_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5___redArg(v_data_5634_);
    return v___x_5635_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_5636_: *mut LeanObject,
    mut v_i_5637_: *mut LeanObject,
    mut v_source_5638_: *mut LeanObject,
    mut v_target_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    v___x_5640_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_i_5637_, v_source_5638_, v_target_5639_);
    return v___x_5640_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8(
    mut v_00_u03b2_5641_: *mut LeanObject,
    mut v_x_5642_: *mut LeanObject,
    mut v_x_5643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    v___x_5644_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Anchor_0__Lean_Meta_Grind_getNumDigitsForAnchors_go___at___00Lean_Meta_Grind_getNumDigitsForAnchors___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms_spec__0_spec__0_spec__2_spec__5_spec__6_spec__8___redArg(v_x_5642_, v_x_5643_);
    return v___x_5644_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1()
-> *mut LeanObject {
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    v___x_5657_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_5658_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__1;
    v___x_5659_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___closed__3;
    v___x_5660_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_5661_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5657_,
        v___x_5658_,
        v___x_5659_,
        v___x_5660_,
    );
    return v___x_5661_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1___boxed(
    mut v_a_5662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5663_: *mut LeanObject = core::ptr::null_mut();
    v_res_5663_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
    return v_res_5663_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(
    mut v_e_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5667_: u8 = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5681_: u8 = 0;
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5687_: u8 = 0;
    let mut v_unused_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5667_ = l_Lean_Expr_hasMVar(v_e_5664_);
                if v___x_5667_ == 0 {
                    v___x_5668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5668_, 0, v_e_5664_);
                    return v___x_5668_;
                } else {
                    v___x_5669_ = lean_st_ref_get(v___y_5665_);
                    v_mctx_5670_ = lean_ctor_get(v___x_5669_, 0);
                    lean_inc_ref(v_mctx_5670_);
                    lean_dec(v___x_5669_);
                    v___x_5671_ = l_Lean_instantiateMVarsCore(v_mctx_5670_, v_e_5664_);
                    v_fst_5672_ = lean_ctor_get(v___x_5671_, 0);
                    lean_inc(v_fst_5672_);
                    v_snd_5673_ = lean_ctor_get(v___x_5671_, 1);
                    lean_inc(v_snd_5673_);
                    lean_dec_ref(v___x_5671_);
                    v___x_5674_ = lean_st_ref_take(v___y_5665_);
                    v_cache_5675_ = lean_ctor_get(v___x_5674_, 1);
                    v_zetaDeltaFVarIds_5676_ = lean_ctor_get(v___x_5674_, 2);
                    v_postponed_5677_ = lean_ctor_get(v___x_5674_, 3);
                    v_diag_5678_ = lean_ctor_get(v___x_5674_, 4);
                    v_isSharedCheck_5687_ = (!lean_is_exclusive(v___x_5674_)) as u8;
                    if v_isSharedCheck_5687_ == 0 {
                        v_unused_5688_ = lean_ctor_get(v___x_5674_, 0);
                        lean_dec(v_unused_5688_);
                        v___x_5680_ = v___x_5674_;
                        v_isShared_5681_ = v_isSharedCheck_5687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_5678_);
                        lean_inc(v_postponed_5677_);
                        lean_inc(v_zetaDeltaFVarIds_5676_);
                        lean_inc(v_cache_5675_);
                        lean_dec(v___x_5674_);
                        v___x_5680_ = lean_box(0);
                        v_isShared_5681_ = v_isSharedCheck_5687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5681_ == 0 {
                    lean_ctor_set(v___x_5680_, 0, v_snd_5673_);
                    v___x_5683_ = v___x_5680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_snd_5673_);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 1, v_cache_5675_);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 2, v_zetaDeltaFVarIds_5676_);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 3, v_postponed_5677_);
                    lean_ctor_set(v_reuseFailAlloc_5686_, 4, v_diag_5678_);
                    v___x_5683_ = v_reuseFailAlloc_5686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5684_ = lean_st_ref_set(v___y_5665_, v___x_5683_);
                v___x_5685_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5685_, 0, v_fst_5672_);
                return v___x_5685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg___boxed(
    mut v_e_5689_: *mut LeanObject,
    mut v___y_5690_: *mut LeanObject,
    mut v___y_5691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5692_: *mut LeanObject = core::ptr::null_mut();
    v_res_5692_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v_e_5689_, v___y_5690_);
    lean_dec(v___y_5690_);
    return v_res_5692_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(
    mut v_e_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5703_: *mut LeanObject = core::ptr::null_mut();
    v___x_5703_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v_e_5693_, v___y_5699_);
    return v___x_5703_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___boxed(
    mut v_e_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
    mut v___y_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5714_: *mut LeanObject = core::ptr::null_mut();
    v_res_5714_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0(v_e_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
    lean_dec(v___y_5712_);
    lean_dec_ref(v___y_5711_);
    lean_dec(v___y_5710_);
    lean_dec_ref(v___y_5709_);
    lean_dec(v___y_5708_);
    lean_dec_ref(v___y_5707_);
    lean_dec(v___y_5706_);
    lean_dec_ref(v___y_5705_);
    return v_res_5714_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(
    mut v_x_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
    mut v___y_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5719_);
    lean_inc_ref(v___y_5718_);
    lean_inc(v___y_5717_);
    lean_inc_ref(v___y_5716_);
    v___x_5725_ = lean_apply_9(
        v_x_5715_,
        v___y_5716_,
        v___y_5717_,
        v___y_5718_,
        v___y_5719_,
        v___y_5720_,
        v___y_5721_,
        v___y_5722_,
        v___y_5723_,
        lean_box(0),
    );
    return v___x_5725_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed(
    mut v_x_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
    mut v___y_5734_: *mut LeanObject,
    mut v___y_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5736_: *mut LeanObject = core::ptr::null_mut();
    v_res_5736_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0(v_x_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
    lean_dec(v___y_5730_);
    lean_dec_ref(v___y_5729_);
    lean_dec(v___y_5728_);
    lean_dec_ref(v___y_5727_);
    return v_res_5736_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(
    mut v_mvarId_5737_: *mut LeanObject,
    mut v_x_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
    mut v___y_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
    mut v___y_5745_: *mut LeanObject,
    mut v___y_5746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5753_: u8 = 0;
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5757_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5742_);
                lean_inc_ref(v___y_5741_);
                lean_inc(v___y_5740_);
                lean_inc_ref(v___y_5739_);
                v___f_5748_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_5748_, 0, v_x_5738_);
                lean_closure_set(v___f_5748_, 1, v___y_5739_);
                lean_closure_set(v___f_5748_, 2, v___y_5740_);
                lean_closure_set(v___f_5748_, 3, v___y_5741_);
                lean_closure_set(v___f_5748_, 4, v___y_5742_);
                v___x_5749_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5737_,
                    v___f_5748_,
                    v___y_5743_,
                    v___y_5744_,
                    v___y_5745_,
                    v___y_5746_,
                );
                if lean_obj_tag(v___x_5749_) == 0 {
                    return v___x_5749_;
                } else {
                    v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
                    v_isSharedCheck_5757_ = (!lean_is_exclusive(v___x_5749_)) as u8;
                    if v_isSharedCheck_5757_ == 0 {
                        v___x_5752_ = v___x_5749_;
                        v_isShared_5753_ = v_isSharedCheck_5757_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5750_);
                        lean_dec(v___x_5749_);
                        v___x_5752_ = lean_box(0);
                        v_isShared_5753_ = v_isSharedCheck_5757_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5753_ == 0 {
                    v___x_5755_ = v___x_5752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5756_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_a_5750_);
                    v___x_5755_ = v_reuseFailAlloc_5756_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg___boxed(
    mut v_mvarId_5758_: *mut LeanObject,
    mut v_x_5759_: *mut LeanObject,
    mut v___y_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5769_: *mut LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_5758_, v_x_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
    lean_dec(v___y_5767_);
    lean_dec_ref(v___y_5766_);
    lean_dec(v___y_5765_);
    lean_dec_ref(v___y_5764_);
    lean_dec(v___y_5763_);
    lean_dec_ref(v___y_5762_);
    lean_dec(v___y_5761_);
    lean_dec_ref(v___y_5760_);
    return v_res_5769_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(
    mut v_00_u03b1_5770_: *mut LeanObject,
    mut v_mvarId_5771_: *mut LeanObject,
    mut v_x_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    v___x_5782_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_5771_, v_x_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_);
    return v___x_5782_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___boxed(
    mut v_00_u03b1_5783_: *mut LeanObject,
    mut v_mvarId_5784_: *mut LeanObject,
    mut v_x_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5795_: *mut LeanObject = core::ptr::null_mut();
    v_res_5795_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1(v_00_u03b1_5783_, v_mvarId_5784_, v_x_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
    lean_dec(v___y_5793_);
    lean_dec_ref(v___y_5792_);
    lean_dec(v___y_5791_);
    lean_dec_ref(v___y_5790_);
    lean_dec(v___y_5789_);
    lean_dec_ref(v___y_5788_);
    lean_dec(v___y_5787_);
    lean_dec_ref(v___y_5786_);
    return v_res_5795_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(
    mut v___x_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__0___redArg(v___x_5796_, v___y_5802_);
    v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
    lean_inc(v_a_5807_);
    lean_dec_ref(v___x_5806_);
    v___x_5808_ = l_Lean_MessageData_ofExpr(v_a_5807_);
    v___x_5809_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__0(v___x_5808_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_, v___y_5804_);
    return v___x_5809_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed(
    mut v___x_5810_: *mut LeanObject,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
    mut v___y_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5820_: *mut LeanObject = core::ptr::null_mut();
    v_res_5820_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0(v___x_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
    lean_dec(v___y_5818_);
    lean_dec_ref(v___y_5817_);
    lean_dec(v___y_5816_);
    lean_dec_ref(v___y_5815_);
    lean_dec(v___y_5814_);
    lean_dec_ref(v___y_5813_);
    lean_dec(v___y_5812_);
    lean_dec_ref(v___y_5811_);
    return v_res_5820_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(
    mut v_stx_5835_: *mut LeanObject,
    mut v_a_5836_: *mut LeanObject,
    mut v_a_5837_: *mut LeanObject,
    mut v_a_5838_: *mut LeanObject,
    mut v_a_5839_: *mut LeanObject,
    mut v_a_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
    mut v_a_5842_: *mut LeanObject,
    mut v_a_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: u8 = 0;
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: u8 = 0;
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5845_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1;
                lean_inc(v_stx_5835_);
                v___x_5846_ = l_Lean_Syntax_isOfKind(v_stx_5835_, v___x_5845_);
                if v___x_5846_ == 0 {
                    lean_dec(v_stx_5835_);
                    v___x_5847_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                    return v___x_5847_;
                } else {
                    v___x_5848_ = lean_unsigned_to_nat(1);
                    v___x_5849_ = l_Lean_Syntax_getArg(v_stx_5835_, v___x_5848_);
                    lean_dec(v_stx_5835_);
                    v___x_5850_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__3;
                    lean_inc(v___x_5849_);
                    v___x_5851_ = l_Lean_Syntax_isOfKind(v___x_5849_, v___x_5850_);
                    if v___x_5851_ == 0 {
                        lean_dec(v___x_5849_);
                        v___x_5852_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted_spec__2___redArg();
                        return v___x_5852_;
                    } else {
                        v___x_5853_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(
                            v_a_5837_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_,
                        );
                        if lean_obj_tag(v___x_5853_) == 0 {
                            v_a_5854_ = lean_ctor_get(v___x_5853_, 0);
                            lean_inc(v_a_5854_);
                            lean_dec_ref_known(v___x_5853_, 1);
                            v___x_5855_ = l_Lean_Elab_Tactic_Grind_evalGrindTactic(
                                v___x_5849_,
                                v_a_5836_,
                                v_a_5837_,
                                v_a_5838_,
                                v_a_5839_,
                                v_a_5840_,
                                v_a_5841_,
                                v_a_5842_,
                                v_a_5843_,
                            );
                            if lean_obj_tag(v___x_5855_) == 0 {
                                lean_dec_ref_known(v___x_5855_, 1);
                                v_mvarId_5856_ = lean_ctor_get(v_a_5854_, 1);
                                lean_inc_n(v_mvarId_5856_, 2);
                                lean_dec(v_a_5854_);
                                v___x_5857_ = l_Lean_mkMVar(v_mvarId_5856_);
                                v___f_5858_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                                lean_closure_set(v___f_5858_, 0, v___x_5857_);
                                v___x_5859_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm_spec__1___redArg(v_mvarId_5856_, v___f_5858_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_, v_a_5843_);
                                return v___x_5859_;
                            } else {
                                lean_dec(v_a_5854_);
                                return v___x_5855_;
                            }
                        } else {
                            lean_dec(v___x_5849_);
                            v_a_5860_ = lean_ctor_get(v___x_5853_, 0);
                            v_isSharedCheck_5867_ = (!lean_is_exclusive(v___x_5853_)) as u8;
                            if v_isSharedCheck_5867_ == 0 {
                                v___x_5862_ = v___x_5853_;
                                v_isShared_5863_ = v_isSharedCheck_5867_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5860_);
                                lean_dec(v___x_5853_);
                                v___x_5862_ = lean_box(0);
                                v_isShared_5863_ = v_isSharedCheck_5867_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5863_ == 0 {
                    v___x_5865_ = v___x_5862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
                    v___x_5865_ = v_reuseFailAlloc_5866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed(
    mut v_stx_5868_: *mut LeanObject,
    mut v_a_5869_: *mut LeanObject,
    mut v_a_5870_: *mut LeanObject,
    mut v_a_5871_: *mut LeanObject,
    mut v_a_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
    mut v_a_5877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5878_: *mut LeanObject = core::ptr::null_mut();
    v_res_5878_ =
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm(
            v_stx_5868_,
            v_a_5869_,
            v_a_5870_,
            v_a_5871_,
            v_a_5872_,
            v_a_5873_,
            v_a_5874_,
            v_a_5875_,
            v_a_5876_,
        );
    lean_dec(v_a_5876_);
    lean_dec_ref(v_a_5875_);
    lean_dec(v_a_5874_);
    lean_dec_ref(v_a_5873_);
    lean_dec(v_a_5872_);
    lean_dec_ref(v_a_5871_);
    lean_dec(v_a_5870_);
    lean_dec_ref(v_a_5869_);
    return v_res_5878_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1()
-> *mut LeanObject {
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    v___x_5884_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
    v___x_5885_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___closed__1;
    v___x_5886_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___closed__1;
    v___x_5887_ = lean_alloc_closure(
        l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___boxed
            as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5888_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5884_,
        v___x_5885_,
        v___x_5886_,
        v___x_5887_,
    );
    return v___x_5888_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1___boxed(
    mut v_a_5889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5890_: *mut LeanObject = core::ptr::null_mut();
    v_res_5890_ = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
    return v_res_5890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowAsserted__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTrue__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowFalse__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowEqcs__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowState__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowCases__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowLocalThms__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm___regBuiltin___private_Lean_Elab_Tactic_Grind_ShowState_0__Lean_Elab_Tactic_Grind_evalShowTerm__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_ShowState(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Filter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
}
