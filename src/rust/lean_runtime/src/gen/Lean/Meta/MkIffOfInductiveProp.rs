// Lean compiler output
// Module: Lean.Meta.MkIffOfInductiveProp
// Imports: Lean.Meta.Basic Lean.Elab.Tactic.Basic Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Cases
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_drop___redArg, l_List_reverse___redArg,
    l_List_unzipTR___redArg, l_List_zipWith___at___00List_zip_spec__0,
};
use crate::r#gen::Init::Data::List::BasicAux::l_List_getLast_x21___redArg;
use crate::r#gen::Init::Data::List::Impl::{
    l___private_Init_Data_List_Impl_0__List_takeTR_go, l_List_zipIdxTR___redArg,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_replaceRef,
    l_List_get___redArg, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_evalTactic,
    l_Lean_Elab_Tactic_run___boxed, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_TermElabM_run___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_ConstantInfo_instantiateTypeLevelParams, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_const___override,
    l_Lean_Expr_fvar___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar, l_Lean_Expr_isProp, l_Lean_Expr_lam___override,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_replaceFVar, l_Lean_Expr_replaceFVars,
    l_Lean_Expr_sort___override, l_Lean_Expr_sortLevel_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_getFVarIds;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getType___redArg,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkLambdaFVars, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_MVarId_apply,
    runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_MVarId_cases,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::l_Lean_MVarId_tryClear;
use crate::r#gen::Lean::Meta::Tactic::Intro::{l_Lean_MVarId_intros, l_Lean_Meta_intro1Core};
use crate::r#gen::Lean::Meta::Tactic::Revert::l_Lean_MVarId_revert;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType, l_Lean_MVarId_getType_x27,
    l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_mk,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Level::lean_level_eq;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 102, 105, 110, 101, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value) as *mut LeanObject;
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3_value) as *mut LeanObject,17704266427038597681 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 110, 111, 110, 121, 109, 111, 117, 115, 67, 116, 111, 114, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value) as *mut LeanObject;
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__6_value) as *mut LeanObject,13429426995999683896 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__9_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value) as *mut LeanObject;
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__5_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__11_value) as *mut LeanObject,11921244625177918938 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 119, 111, 32, 115, 117, 98, 103, 111, 97, 108, 115, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0_value) as *mut LeanObject;
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value: LeanCtorObject<10> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*8 + 16) as u16, other: 8, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4_value) as *mut LeanObject,16843009 as *mut LeanObject,65537 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6_value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 100, 101, 120, 32, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 44, 32, 111, 110, 108, 121, 32, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [32, 116, 97, 99, 116, 105, 99, 32, 119, 111, 114, 107, 115, 32, 102, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115, 32, 119, 105, 116, 104, 32, 101, 120, 97, 99, 116, 108, 121, 32, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 102, 116, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__0_value
        ) as *mut LeanObject,
        678391788580772366 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 108, 121, 32, 111, 110, 101, 32, 110,
        101, 119, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__5_value
        ) as *mut LeanObject,
        17832044880651236544 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 97, 105, 108, 101, 100, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 107, 73, 102, 102, 79, 102, 73, 110, 100, 117, 99, 116, 105, 118, 101, 80, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1_value: LeanStringObject<77> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 77, m_capacity: 77, m_length: 76, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 107, 73, 102, 102, 79, 102, 73, 110, 100, 117, 99, 116, 105, 118, 101, 80, 114, 111, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 117, 112, 100, 97, 116, 101, 76, 97, 109, 98, 100, 97, 66, 105, 110, 100, 101, 114, 73, 110, 102, 111, 68, 33, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [108, 97, 109, 98, 100, 97, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [69, 120, 105, 115, 116, 115, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__0_value) as *mut LeanObject,5086165725197901121 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__2_value) as *mut LeanObject,9743492140944907313 as *mut LeanObject] };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3_value) as *mut LeanObject;
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__0_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [79, 114, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__0_value
        ) as *mut LeanObject,
        14181099489592536354 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 97, 108, 115, 101, 0],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__3_value
        ) as *mut LeanObject,
        907667957179513571 as *mut LeanObject,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__0_value) as *mut LeanObject,13589827700912665667 as *mut LeanObject] };
static mut l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value) as *mut LeanObject;
pub static l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__2_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0_value) as *mut LeanObject,980513800819686544 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 111, 32, 115, 117, 98, 103, 111, 97, 108, 115, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 118, 97, 114, 0,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 119, 111, 32, 99, 97, 115, 101, 32, 115,
        117, 98, 103, 111, 97, 108, 115, 0,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0_value:
    LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 99, 97, 115, 101, 32, 115,
        117, 98, 103, 111, 97, 108, 115, 0,
    ],
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0_value) as *mut LeanObject;
pub static l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 101, 32, 99, 97, 115, 101, 32, 115, 117, 98, 103, 111, 97, 108, 0]};
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0_value) as *mut LeanObject;
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [109, 107, 95, 105, 102, 102, 32, 111, 110, 108, 121, 32, 97, 112, 112, 108, 105, 101, 115, 32, 116, 111, 32, 112, 114, 111, 112, 45, 118, 97, 108, 117, 101, 100, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 112, 108, 105, 116, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__0_value) as *mut LeanObject,9917798623386220051 as *mut LeanObject] };
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__2_value) as *mut LeanObject,12124685706703772592 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [16777472 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__6_value) as *mut LeanObject,5617260025639121538 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [77, 107, 73, 102, 102, 79, 102, 73, 110, 100, 117, 99, 116, 105, 118, 101, 80, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value) as *mut LeanObject,17445230330699844781 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__11_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [84, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 112, 114, 111, 111, 102, 32, 111, 102, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 99, 101, 58, 32, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [69, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 32, 102, 111, 114, 109, 32, 105, 115, 58, 32, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSumOfProducts___closed__0_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        101, 120, 105, 115, 116, 101, 110, 116, 105, 97, 108, 95, 101, 113, 117, 105, 118, 0,
    ],
};
static mut l_Lean_Meta_mkSumOfProducts___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSumOfProducts___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_mkSumOfProducts___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_mkSumOfProducts___closed__0_value) as *mut LeanObject,
        7633731374219804931 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_mkSumOfProducts___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSumOfProducts___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_mkSumOfProducts___closed__2_value: LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        78, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 97, 32, 100, 101, 102, 105, 110,
        105, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_mkSumOfProducts___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSumOfProducts___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_mkSumOfProducts___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkSumOfProducts___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkSumOfProducts___closed__4_value: LeanStringObject<32> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        71, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 101, 120, 105, 115, 116, 101, 110, 116,
        105, 97, 108, 32, 102, 111, 114, 109, 32, 111, 102, 32, 0,
    ],
};
static mut l_Lean_Meta_mkSumOfProducts___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkSumOfProducts___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_mkSumOfProducts___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkSumOfProducts___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value) as *mut LeanObject,7692429399689152900 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,17722750404649329381 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,4106845723219969456 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value) as *mut LeanObject,128205165616414140 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,14615797341979344201 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,3330899362460428516 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__0_value) as *mut LeanObject,7269408049546915141 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__8_value) as *mut LeanObject,15277341936020051245 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__9_value) as *mut LeanObject,6982407890357886803 as *mut LeanObject] };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(
    mut v_x_3810_: *mut LeanObject,
) -> u8 {
    let mut v___x_3811_: u8 = 0;
    v___x_3811_ = 0;
    return v___x_3811_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0___boxed(
    mut v_x_3812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3813_: u8 = 0;
    let mut v_r_3814_: *mut LeanObject = core::ptr::null_mut();
    v_res_3813_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__0(v_x_3812_);
    lean_dec(v_x_3812_);
    v_r_3814_ = lean_box((v_res_3813_) as usize);
    return v_r_3814_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(
    mut v_x_3815_: *mut LeanObject,
    mut v_x_3816_: *mut LeanObject,
    mut v_x_3817_: *mut LeanObject,
    mut v_x_3818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3823_: u8 = 0;
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3819_ = lean_ctor_get(v_x_3815_, 0);
                v_vs_3820_ = lean_ctor_get(v_x_3815_, 1);
                v_isSharedCheck_3844_ = (!lean_is_exclusive(v_x_3815_)) as u8;
                if v_isSharedCheck_3844_ == 0 {
                    v___x_3822_ = v_x_3815_;
                    v_isShared_3823_ = v_isSharedCheck_3844_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3820_);
                    lean_inc(v_ks_3819_);
                    lean_dec(v_x_3815_);
                    v___x_3822_ = lean_box(0);
                    v_isShared_3823_ = v_isSharedCheck_3844_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3824_ = lean_array_get_size(v_ks_3819_);
                v___x_3825_ = lean_nat_dec_lt(v_x_3816_, v___x_3824_);
                if v___x_3825_ == 0 {
                    lean_dec(v_x_3816_);
                    v___x_3826_ = lean_array_push(v_ks_3819_, v_x_3817_);
                    v___x_3827_ = lean_array_push(v_vs_3820_, v_x_3818_);
                    if v_isShared_3823_ == 0 {
                        lean_ctor_set(v___x_3822_, 1, v___x_3827_);
                        lean_ctor_set(v___x_3822_, 0, v___x_3826_);
                        v___x_3829_ = v___x_3822_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3826_);
                        lean_ctor_set(v_reuseFailAlloc_3830_, 1, v___x_3827_);
                        v___x_3829_ = v_reuseFailAlloc_3830_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3831_ = lean_array_fget_borrowed(v_ks_3819_, v_x_3816_);
                    v___x_3832_ = l_Lean_instBEqMVarId_beq(v_x_3817_, v_k_x27_3831_);
                    if v___x_3832_ == 0 {
                        if v_isShared_3823_ == 0 {
                            v___x_3834_ = v___x_3822_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_ks_3819_);
                            lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_vs_3820_);
                            v___x_3834_ = v_reuseFailAlloc_3838_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3839_ = lean_array_fset(v_ks_3819_, v_x_3816_, v_x_3817_);
                        v___x_3840_ = lean_array_fset(v_vs_3820_, v_x_3816_, v_x_3818_);
                        lean_dec(v_x_3816_);
                        if v_isShared_3823_ == 0 {
                            lean_ctor_set(v___x_3822_, 1, v___x_3840_);
                            lean_ctor_set(v___x_3822_, 0, v___x_3839_);
                            v___x_3842_ = v___x_3822_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3839_);
                            lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3840_);
                            v___x_3842_ = v_reuseFailAlloc_3843_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3829_;
            }
            3 => {
                v___x_3835_ = lean_unsigned_to_nat(1);
                v___x_3836_ = lean_nat_add(v_x_3816_, v___x_3835_);
                lean_dec(v_x_3816_);
                v_x_3815_ = v___x_3834_;
                v_x_3816_ = v___x_3836_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_n_3845_: *mut LeanObject,
    mut v_k_3846_: *mut LeanObject,
    mut v_v_3847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    v___x_3848_ = lean_unsigned_to_nat(0);
    v___x_3849_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_n_3845_, v___x_3848_, v_k_3846_, v_v_3847_);
    return v___x_3849_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_3850_: usize = 0;
    let mut v___x_3851_: usize = 0;
    let mut v___x_3852_: usize = 0;
    v___x_3850_ = 5usize;
    v___x_3851_ = 1usize;
    v___x_3852_ = lean_usize_shift_left(v___x_3851_, v___x_3850_);
    return v___x_3852_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_3853_: usize = 0;
    let mut v___x_3854_: usize = 0;
    let mut v___x_3855_: usize = 0;
    v___x_3853_ = 1usize;
    v___x_3854_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__0);
    v___x_3855_ = lean_usize_sub(v___x_3854_, v___x_3853_);
    return v___x_3855_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    v___x_3856_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3856_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(
    mut v_x_3857_: *mut LeanObject,
    mut v_x_3858_: usize,
    mut v_x_3859_: usize,
    mut v_x_3860_: *mut LeanObject,
    mut v_x_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: usize = 0;
    let mut v___x_3864_: usize = 0;
    let mut v___x_3865_: usize = 0;
    let mut v___x_3866_: usize = 0;
    let mut v_j_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v_v_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3893_: u8 = 0;
    let mut v_node_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3897_: u8 = 0;
    let mut v___x_3898_: usize = 0;
    let mut v___x_3899_: usize = 0;
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: u8 = 0;
    let mut v_ks_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: usize = 0;
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3929_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3857_) == 0 {
                    v_es_3862_ = lean_ctor_get(v_x_3857_, 0);
                    v___x_3863_ = 5usize;
                    v___x_3864_ = 1usize;
                    v___x_3865_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__1);
                    v___x_3866_ = lean_usize_land(v_x_3858_, v___x_3865_);
                    v_j_3867_ = lean_usize_to_nat(v___x_3866_);
                    v___x_3868_ = lean_array_get_size(v_es_3862_);
                    v___x_3869_ = lean_nat_dec_lt(v_j_3867_, v___x_3868_);
                    if v___x_3869_ == 0 {
                        lean_dec(v_j_3867_);
                        lean_dec(v_x_3861_);
                        lean_dec(v_x_3860_);
                        return v_x_3857_;
                    } else {
                        lean_inc_ref(v_es_3862_);
                        v_isSharedCheck_3906_ = (!lean_is_exclusive(v_x_3857_)) as u8;
                        if v_isSharedCheck_3906_ == 0 {
                            v_unused_3907_ = lean_ctor_get(v_x_3857_, 0);
                            lean_dec(v_unused_3907_);
                            v___x_3871_ = v_x_3857_;
                            v_isShared_3872_ = v_isSharedCheck_3906_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3857_);
                            v___x_3871_ = lean_box(0);
                            v_isShared_3872_ = v_isSharedCheck_3906_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3908_ = lean_ctor_get(v_x_3857_, 0);
                    v_vs_3909_ = lean_ctor_get(v_x_3857_, 1);
                    v_isSharedCheck_3929_ = (!lean_is_exclusive(v_x_3857_)) as u8;
                    if v_isSharedCheck_3929_ == 0 {
                        v___x_3911_ = v_x_3857_;
                        v_isShared_3912_ = v_isSharedCheck_3929_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3909_);
                        lean_inc(v_ks_3908_);
                        lean_dec(v_x_3857_);
                        v___x_3911_ = lean_box(0);
                        v_isShared_3912_ = v_isSharedCheck_3929_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3873_ = lean_array_fget(v_es_3862_, v_j_3867_);
                v___x_3874_ = lean_box(0);
                v_xs_x27_3875_ = lean_array_fset(v_es_3862_, v_j_3867_, v___x_3874_);
                match lean_obj_tag(v_v_3873_) {
                    0 => {
                        v_key_3882_ = lean_ctor_get(v_v_3873_, 0);
                        v_val_3883_ = lean_ctor_get(v_v_3873_, 1);
                        v_isSharedCheck_3893_ = (!lean_is_exclusive(v_v_3873_)) as u8;
                        if v_isSharedCheck_3893_ == 0 {
                            v___x_3885_ = v_v_3873_;
                            v_isShared_3886_ = v_isSharedCheck_3893_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3883_);
                            lean_inc(v_key_3882_);
                            lean_dec(v_v_3873_);
                            v___x_3885_ = lean_box(0);
                            v_isShared_3886_ = v_isSharedCheck_3893_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3894_ = lean_ctor_get(v_v_3873_, 0);
                        v_isSharedCheck_3904_ = (!lean_is_exclusive(v_v_3873_)) as u8;
                        if v_isSharedCheck_3904_ == 0 {
                            v___x_3896_ = v_v_3873_;
                            v_isShared_3897_ = v_isSharedCheck_3904_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3894_);
                            lean_dec(v_v_3873_);
                            v___x_3896_ = lean_box(0);
                            v_isShared_3897_ = v_isSharedCheck_3904_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3905_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3905_, 0, v_x_3860_);
                        lean_ctor_set(v___x_3905_, 1, v_x_3861_);
                        v___y_3877_ = v___x_3905_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3878_ = lean_array_fset(v_xs_x27_3875_, v_j_3867_, v___y_3877_);
                lean_dec(v_j_3867_);
                if v_isShared_3872_ == 0 {
                    lean_ctor_set(v___x_3871_, 0, v___x_3878_);
                    v___x_3880_ = v___x_3871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3878_);
                    v___x_3880_ = v_reuseFailAlloc_3881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3880_;
            }
            4 => {
                v___x_3887_ = l_Lean_instBEqMVarId_beq(v_x_3860_, v_key_3882_);
                if v___x_3887_ == 0 {
                    lean_del_object(v___x_3885_);
                    v___x_3888_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3882_,
                        v_val_3883_,
                        v_x_3860_,
                        v_x_3861_,
                    );
                    v___x_3889_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3889_, 0, v___x_3888_);
                    v___y_3877_ = v___x_3889_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3883_);
                    lean_dec(v_key_3882_);
                    if v_isShared_3886_ == 0 {
                        lean_ctor_set(v___x_3885_, 1, v_x_3861_);
                        lean_ctor_set(v___x_3885_, 0, v_x_3860_);
                        v___x_3891_ = v___x_3885_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_x_3860_);
                        lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_x_3861_);
                        v___x_3891_ = v_reuseFailAlloc_3892_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3877_ = v___x_3891_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3898_ = lean_usize_shift_right(v_x_3858_, v___x_3863_);
                v___x_3899_ = lean_usize_add(v_x_3859_, v___x_3864_);
                v___x_3900_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_node_3894_, v___x_3898_, v___x_3899_, v_x_3860_, v_x_3861_);
                if v_isShared_3897_ == 0 {
                    lean_ctor_set(v___x_3896_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3896_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3877_ = v___x_3902_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_ks_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_vs_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3928_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3915_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v___x_3914_, v_x_3860_, v_x_3861_);
                v___x_3923_ = 7usize;
                v___x_3924_ = lean_usize_dec_le(v___x_3923_, v_x_3859_);
                if v___x_3924_ == 0 {
                    v___x_3925_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3915_);
                    v___x_3926_ = lean_unsigned_to_nat(4);
                    v___x_3927_ = lean_nat_dec_lt(v___x_3925_, v___x_3926_);
                    lean_dec(v___x_3925_);
                    v___y_3917_ = v___x_3927_;
                    state = 10;
                    continue;
                } else {
                    v___y_3917_ = v___x_3924_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3917_ == 0 {
                    v_ks_3918_ = lean_ctor_get(v_newNode_3915_, 0);
                    lean_inc_ref(v_ks_3918_);
                    v_vs_3919_ = lean_ctor_get(v_newNode_3915_, 1);
                    lean_inc_ref(v_vs_3919_);
                    lean_dec_ref(v_newNode_3915_);
                    v___x_3920_ = lean_unsigned_to_nat(0);
                    v___x_3921_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___closed__2);
                    v___x_3922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_x_3859_, v_ks_3918_, v_vs_3919_, v___x_3920_, v___x_3921_);
                    lean_dec_ref(v_vs_3919_);
                    lean_dec_ref(v_ks_3918_);
                    return v___x_3922_;
                } else {
                    return v_newNode_3915_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(
    mut v_depth_3930_: usize,
    mut v_keys_3931_: *mut LeanObject,
    mut v_vals_3932_: *mut LeanObject,
    mut v_i_3933_: *mut LeanObject,
    mut v_entries_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: u8 = 0;
    let mut v_k_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u64 = 0;
    let mut v_h_3940_: usize = 0;
    let mut v___x_3941_: usize = 0;
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: usize = 0;
    let mut v___x_3944_: usize = 0;
    let mut v___x_3945_: usize = 0;
    let mut v_h_3946_: usize = 0;
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3935_ = lean_array_get_size(v_keys_3931_);
                v___x_3936_ = lean_nat_dec_lt(v_i_3933_, v___x_3935_);
                if v___x_3936_ == 0 {
                    lean_dec(v_i_3933_);
                    return v_entries_3934_;
                } else {
                    v_k_3937_ = lean_array_fget_borrowed(v_keys_3931_, v_i_3933_);
                    v_v_3938_ = lean_array_fget_borrowed(v_vals_3932_, v_i_3933_);
                    v___x_3939_ = l_Lean_instHashableMVarId_hash(v_k_3937_);
                    v_h_3940_ = lean_uint64_to_usize(v___x_3939_);
                    v___x_3941_ = 5usize;
                    v___x_3942_ = lean_unsigned_to_nat(1);
                    v___x_3943_ = 1usize;
                    v___x_3944_ = lean_usize_sub(v_depth_3930_, v___x_3943_);
                    v___x_3945_ = lean_usize_mul(v___x_3941_, v___x_3944_);
                    v_h_3946_ = lean_usize_shift_right(v_h_3940_, v___x_3945_);
                    v___x_3947_ = lean_nat_add(v_i_3933_, v___x_3942_);
                    lean_dec(v_i_3933_);
                    lean_inc(v_v_3938_);
                    lean_inc(v_k_3937_);
                    v___x_3948_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_entries_3934_, v_h_3946_, v_depth_3930_, v_k_3937_, v_v_3938_);
                    v_i_3933_ = v___x_3947_;
                    v_entries_3934_ = v___x_3948_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_depth_3950_: *mut LeanObject,
    mut v_keys_3951_: *mut LeanObject,
    mut v_vals_3952_: *mut LeanObject,
    mut v_i_3953_: *mut LeanObject,
    mut v_entries_3954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3955_: usize = 0;
    let mut v_res_3956_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3955_ = lean_unbox_usize(v_depth_3950_);
    lean_dec(v_depth_3950_);
    v_res_3956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_boxed_3955_, v_keys_3951_, v_vals_3952_, v_i_3953_, v_entries_3954_);
    lean_dec_ref(v_vals_3952_);
    lean_dec_ref(v_keys_3951_);
    return v_res_3956_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_x_3957_: *mut LeanObject,
    mut v_x_3958_: *mut LeanObject,
    mut v_x_3959_: *mut LeanObject,
    mut v_x_3960_: *mut LeanObject,
    mut v_x_3961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4204__boxed_3962_: usize = 0;
    let mut v_x_4205__boxed_3963_: usize = 0;
    let mut v_res_3964_: *mut LeanObject = core::ptr::null_mut();
    v_x_4204__boxed_3962_ = lean_unbox_usize(v_x_3958_);
    lean_dec(v_x_3958_);
    v_x_4205__boxed_3963_ = lean_unbox_usize(v_x_3959_);
    lean_dec(v_x_3959_);
    v_res_3964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_3957_, v_x_4204__boxed_3962_, v_x_4205__boxed_3963_, v_x_3960_, v_x_3961_);
    return v_res_3964_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(
    mut v_x_3965_: *mut LeanObject,
    mut v_x_3966_: *mut LeanObject,
    mut v_x_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3968_: u64 = 0;
    let mut v___x_3969_: usize = 0;
    let mut v___x_3970_: usize = 0;
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    v___x_3968_ = l_Lean_instHashableMVarId_hash(v_x_3966_);
    v___x_3969_ = lean_uint64_to_usize(v___x_3968_);
    v___x_3970_ = 1usize;
    v___x_3971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_3965_, v___x_3969_, v___x_3970_, v_x_3966_, v_x_3967_);
    return v___x_3971_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(
    mut v_mvarId_3972_: *mut LeanObject,
    mut v_val_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3984_: u8 = 0;
    let mut v_depth_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4008_: u8 = 0;
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3976_ = lean_st_ref_take(v___y_3974_);
                v_mctx_3977_ = lean_ctor_get(v___x_3976_, 0);
                v_cache_3978_ = lean_ctor_get(v___x_3976_, 1);
                v_zetaDeltaFVarIds_3979_ = lean_ctor_get(v___x_3976_, 2);
                v_postponed_3980_ = lean_ctor_get(v___x_3976_, 3);
                v_diag_3981_ = lean_ctor_get(v___x_3976_, 4);
                v_isSharedCheck_4009_ = (!lean_is_exclusive(v___x_3976_)) as u8;
                if v_isSharedCheck_4009_ == 0 {
                    v___x_3983_ = v___x_3976_;
                    v_isShared_3984_ = v_isSharedCheck_4009_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3981_);
                    lean_inc(v_postponed_3980_);
                    lean_inc(v_zetaDeltaFVarIds_3979_);
                    lean_inc(v_cache_3978_);
                    lean_inc(v_mctx_3977_);
                    lean_dec(v___x_3976_);
                    v___x_3983_ = lean_box(0);
                    v_isShared_3984_ = v_isSharedCheck_4009_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3985_ = lean_ctor_get(v_mctx_3977_, 0);
                v_levelAssignDepth_3986_ = lean_ctor_get(v_mctx_3977_, 1);
                v_lmvarCounter_3987_ = lean_ctor_get(v_mctx_3977_, 2);
                v_mvarCounter_3988_ = lean_ctor_get(v_mctx_3977_, 3);
                v_lDecls_3989_ = lean_ctor_get(v_mctx_3977_, 4);
                v_decls_3990_ = lean_ctor_get(v_mctx_3977_, 5);
                v_userNames_3991_ = lean_ctor_get(v_mctx_3977_, 6);
                v_lAssignment_3992_ = lean_ctor_get(v_mctx_3977_, 7);
                v_eAssignment_3993_ = lean_ctor_get(v_mctx_3977_, 8);
                v_dAssignment_3994_ = lean_ctor_get(v_mctx_3977_, 9);
                v_isSharedCheck_4008_ = (!lean_is_exclusive(v_mctx_3977_)) as u8;
                if v_isSharedCheck_4008_ == 0 {
                    v___x_3996_ = v_mctx_3977_;
                    v_isShared_3997_ = v_isSharedCheck_4008_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3994_);
                    lean_inc(v_eAssignment_3993_);
                    lean_inc(v_lAssignment_3992_);
                    lean_inc(v_userNames_3991_);
                    lean_inc(v_decls_3990_);
                    lean_inc(v_lDecls_3989_);
                    lean_inc(v_mvarCounter_3988_);
                    lean_inc(v_lmvarCounter_3987_);
                    lean_inc(v_levelAssignDepth_3986_);
                    lean_inc(v_depth_3985_);
                    lean_dec(v_mctx_3977_);
                    v___x_3996_ = lean_box(0);
                    v_isShared_3997_ = v_isSharedCheck_4008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3998_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_eAssignment_3993_, v_mvarId_3972_, v_val_3973_);
                if v_isShared_3997_ == 0 {
                    lean_ctor_set(v___x_3996_, 8, v___x_3998_);
                    v___x_4000_ = v___x_3996_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_depth_3985_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_levelAssignDepth_3986_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 2, v_lmvarCounter_3987_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 3, v_mvarCounter_3988_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 4, v_lDecls_3989_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 5, v_decls_3990_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 6, v_userNames_3991_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 7, v_lAssignment_3992_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 8, v___x_3998_);
                    lean_ctor_set(v_reuseFailAlloc_4007_, 9, v_dAssignment_3994_);
                    v___x_4000_ = v_reuseFailAlloc_4007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3984_ == 0 {
                    lean_ctor_set(v___x_3983_, 0, v___x_4000_);
                    v___x_4002_ = v___x_3983_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4000_);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_cache_3978_);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_zetaDeltaFVarIds_3979_);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 3, v_postponed_3980_);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 4, v_diag_3981_);
                    v___x_4002_ = v_reuseFailAlloc_4006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4003_ = lean_st_ref_set(v___y_3974_, v___x_4002_);
                v___x_4004_ = lean_box(0);
                v___x_4005_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4005_, 0, v___x_4004_);
                return v___x_4005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg___boxed(
    mut v_mvarId_4010_: *mut LeanObject,
    mut v_val_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4014_: *mut LeanObject = core::ptr::null_mut();
    v_res_4014_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_4010_, v_val_4011_, v___y_4012_);
    lean_dec(v___y_4012_);
    return v_res_4014_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: u8 = 0;
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4054_ = lean_ctor_get(v___y_4051_, 5);
    v___x_4055_ = 0;
    v___x_4056_ = l_Lean_SourceInfo_fromRef(v_ref_4054_, v___x_4055_);
    v___x_4057_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3;
    v___x_4058_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4;
    lean_inc_n(v___x_4056_, 9);
    v___x_4059_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4059_, 0, v___x_4056_);
    lean_ctor_set(v___x_4059_, 1, v___x_4057_);
    v___x_4060_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7;
    v___x_4061_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8;
    v___x_4062_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4062_, 0, v___x_4056_);
    lean_ctor_set(v___x_4062_, 1, v___x_4061_);
    v___x_4063_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10;
    v___x_4064_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12;
    v___x_4065_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13;
    v___x_4066_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4066_, 0, v___x_4056_);
    lean_ctor_set(v___x_4066_, 1, v___x_4065_);
    v___x_4067_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14;
    v___x_4068_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4068_, 0, v___x_4056_);
    lean_ctor_set(v___x_4068_, 1, v___x_4067_);
    v___x_4069_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4064_, v___x_4066_, v___x_4068_);
    v___x_4070_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15;
    v___x_4071_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4071_, 0, v___x_4056_);
    lean_ctor_set(v___x_4071_, 1, v___x_4070_);
    lean_inc(v___x_4069_);
    v___x_4072_ = l_Lean_Syntax_node3(
        v___x_4056_,
        v___x_4063_,
        v___x_4069_,
        v___x_4071_,
        v___x_4069_,
    );
    v___x_4073_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16;
    v___x_4074_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4074_, 0, v___x_4056_);
    lean_ctor_set(v___x_4074_, 1, v___x_4073_);
    v___x_4075_ = l_Lean_Syntax_node3(
        v___x_4056_,
        v___x_4060_,
        v___x_4062_,
        v___x_4072_,
        v___x_4074_,
    );
    v___x_4076_ = l_Lean_Syntax_node2(v___x_4056_, v___x_4058_, v___x_4059_, v___x_4075_);
    v___x_4077_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_4076_,
        v___y_4045_,
        v___y_4046_,
        v___y_4047_,
        v___y_4048_,
        v___y_4049_,
        v___y_4050_,
        v___y_4051_,
        v___y_4052_,
    );
    return v___x_4077_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___boxed(
    mut v___y_4078_: *mut LeanObject,
    mut v___y_4079_: *mut LeanObject,
    mut v___y_4080_: *mut LeanObject,
    mut v___y_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
    mut v___y_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4087_: *mut LeanObject = core::ptr::null_mut();
    v_res_4087_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1(v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
    lean_dec(v___y_4085_);
    lean_dec_ref(v___y_4084_);
    lean_dec(v___y_4083_);
    lean_dec_ref(v___y_4082_);
    lean_dec(v___y_4081_);
    lean_dec_ref(v___y_4080_);
    lean_dec(v___y_4079_);
    lean_dec_ref(v___y_4078_);
    return v_res_4087_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(
    mut v_msgData_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    v___x_4094_ = lean_st_ref_get(v___y_4092_);
    v_env_4095_ = lean_ctor_get(v___x_4094_, 0);
    lean_inc_ref(v_env_4095_);
    lean_dec(v___x_4094_);
    v___x_4096_ = lean_st_ref_get(v___y_4090_);
    v_mctx_4097_ = lean_ctor_get(v___x_4096_, 0);
    lean_inc_ref(v_mctx_4097_);
    lean_dec(v___x_4096_);
    v_lctx_4098_ = lean_ctor_get(v___y_4089_, 2);
    v_options_4099_ = lean_ctor_get(v___y_4091_, 2);
    lean_inc_ref(v_options_4099_);
    lean_inc_ref(v_lctx_4098_);
    v___x_4100_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4100_, 0, v_env_4095_);
    lean_ctor_set(v___x_4100_, 1, v_mctx_4097_);
    lean_ctor_set(v___x_4100_, 2, v_lctx_4098_);
    lean_ctor_set(v___x_4100_, 3, v_options_4099_);
    v___x_4101_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4101_, 0, v___x_4100_);
    lean_ctor_set(v___x_4101_, 1, v_msgData_4088_);
    v___x_4102_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4102_, 0, v___x_4101_);
    return v___x_4102_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0___boxed(
    mut v_msgData_4103_: *mut LeanObject,
    mut v___y_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4109_: *mut LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msgData_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
    lean_dec(v___y_4107_);
    lean_dec_ref(v___y_4106_);
    lean_dec(v___y_4105_);
    lean_dec_ref(v___y_4104_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(
    mut v_msg_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4116_ = lean_ctor_get(v___y_4113_, 5);
                v___x_4117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
                v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
                v_isSharedCheck_4126_ = (!lean_is_exclusive(v___x_4117_)) as u8;
                if v_isSharedCheck_4126_ == 0 {
                    v___x_4120_ = v___x_4117_;
                    v_isShared_4121_ = v_isSharedCheck_4126_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4118_);
                    lean_dec(v___x_4117_);
                    v___x_4120_ = lean_box(0);
                    v_isShared_4121_ = v_isSharedCheck_4126_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4116_);
                v___x_4122_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4122_, 0, v_ref_4116_);
                lean_ctor_set(v___x_4122_, 1, v_a_4118_);
                if v_isShared_4121_ == 0 {
                    lean_ctor_set_tag(v___x_4120_, 1);
                    lean_ctor_set(v___x_4120_, 0, v___x_4122_);
                    v___x_4124_ = v___x_4120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v___x_4122_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg___boxed(
    mut v_msg_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4133_: *mut LeanObject = core::ptr::null_mut();
    v_res_4133_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
    lean_dec(v___y_4131_);
    lean_dec_ref(v___y_4130_);
    lean_dec(v___y_4129_);
    lean_dec_ref(v___y_4128_);
    return v_res_4133_;
}
pub unsafe fn _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    v___x_4135_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__0;
    v___x_4136_ = l_Lean_stringToMessageData(v___x_4135_);
    return v___x_4136_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(
    mut v_x_4152_: *mut LeanObject,
    mut v_x_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4153_) == 0 {
                    v___x_4159_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4159_, 0, v_x_4152_);
                    return v___x_4159_;
                } else {
                    v_head_4160_ = lean_ctor_get(v_x_4153_, 0);
                    lean_inc(v_head_4160_);
                    v_tail_4161_ = lean_ctor_get(v_x_4153_, 1);
                    lean_inc(v_tail_4161_);
                    lean_dec_ref_known(v_x_4153_, 2);
                    v___f_4169_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__3;
                    v___x_4170_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_4170_, 0, v_x_4152_);
                    lean_closure_set(v___x_4170_, 1, v___f_4169_);
                    v___x_4171_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__5;
                    v___x_4172_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6;
                    v___x_4173_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                        v___x_4170_,
                        v___x_4171_,
                        v___x_4172_,
                        v___y_4154_,
                        v___y_4155_,
                        v___y_4156_,
                        v___y_4157_,
                    );
                    if lean_obj_tag(v___x_4173_) == 0 {
                        v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
                        lean_inc(v_a_4174_);
                        lean_dec_ref_known(v___x_4173_, 1);
                        v_fst_4175_ = lean_ctor_get(v_a_4174_, 0);
                        lean_inc(v_fst_4175_);
                        lean_dec(v_a_4174_);
                        if lean_obj_tag(v_fst_4175_) == 1 {
                            v_tail_4176_ = lean_ctor_get(v_fst_4175_, 1);
                            lean_inc(v_tail_4176_);
                            if lean_obj_tag(v_tail_4176_) == 1 {
                                v_tail_4177_ = lean_ctor_get(v_tail_4176_, 1);
                                if lean_obj_tag(v_tail_4177_) == 0 {
                                    v_head_4178_ = lean_ctor_get(v_fst_4175_, 0);
                                    lean_inc(v_head_4178_);
                                    lean_dec_ref_known(v_fst_4175_, 2);
                                    v_head_4179_ = lean_ctor_get(v_tail_4176_, 0);
                                    lean_inc(v_head_4179_);
                                    lean_dec_ref_known(v_tail_4176_, 2);
                                    v___x_4180_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_head_4178_, v_head_4160_, v___y_4155_);
                                    lean_dec_ref(v___x_4180_);
                                    v_x_4152_ = v_head_4179_;
                                    v_x_4153_ = v_tail_4161_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v_tail_4176_, 2);
                                    lean_dec_ref_known(v_fst_4175_, 2);
                                    lean_dec(v_tail_4161_);
                                    lean_dec(v_head_4160_);
                                    v___y_4163_ = v___y_4154_;
                                    v___y_4164_ = v___y_4155_;
                                    v___y_4165_ = v___y_4156_;
                                    v___y_4166_ = v___y_4157_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_tail_4176_);
                                lean_dec_ref_known(v_fst_4175_, 2);
                                lean_dec(v_tail_4161_);
                                lean_dec(v_head_4160_);
                                v___y_4163_ = v___y_4154_;
                                v___y_4164_ = v___y_4155_;
                                v___y_4165_ = v___y_4156_;
                                v___y_4166_ = v___y_4157_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_4175_);
                            lean_dec(v_tail_4161_);
                            lean_dec(v_head_4160_);
                            v___y_4163_ = v___y_4154_;
                            v___y_4164_ = v___y_4155_;
                            v___y_4165_ = v___y_4156_;
                            v___y_4166_ = v___y_4157_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_tail_4161_);
                        lean_dec(v_head_4160_);
                        v_a_4182_ = lean_ctor_get(v___x_4173_, 0);
                        v_isSharedCheck_4189_ = (!lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4189_ == 0 {
                            v___x_4184_ = v___x_4173_;
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4182_);
                            lean_dec(v___x_4173_);
                            v___x_4184_ = lean_box(0);
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4167_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once), _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
                v___x_4168_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_4167_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
                return v___x_4168_;
            }
            2 => {
                if v_isShared_4185_ == 0 {
                    v___x_4187_ = v___x_4184_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
                    v___x_4187_ = v_reuseFailAlloc_4188_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___boxed(
    mut v_x_4190_: *mut LeanObject,
    mut v_x_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4197_: *mut LeanObject = core::ptr::null_mut();
    v_res_4197_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_x_4190_, v_x_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
    lean_dec(v___y_4195_);
    lean_dec_ref(v___y_4194_);
    lean_dec(v___y_4193_);
    lean_dec_ref(v___y_4192_);
    return v_res_4197_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(
    mut v_mvar_4198_: *mut LeanObject,
    mut v_es_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    v___x_4205_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_mvar_4198_, v_es_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
    return v___x_4205_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi___boxed(
    mut v_mvar_4206_: *mut LeanObject,
    mut v_es_4207_: *mut LeanObject,
    mut v_a_4208_: *mut LeanObject,
    mut v_a_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
    mut v_a_4211_: *mut LeanObject,
    mut v_a_4212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4213_: *mut LeanObject = core::ptr::null_mut();
    v_res_4213_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi(
        v_mvar_4206_,
        v_es_4207_,
        v_a_4208_,
        v_a_4209_,
        v_a_4210_,
        v_a_4211_,
    );
    lean_dec(v_a_4211_);
    lean_dec_ref(v_a_4210_);
    lean_dec(v_a_4209_);
    lean_dec_ref(v_a_4208_);
    return v_res_4213_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(
    mut v_00_u03b1_4214_: *mut LeanObject,
    mut v_msg_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    v___x_4221_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
    return v___x_4221_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___boxed(
    mut v_00_u03b1_4222_: *mut LeanObject,
    mut v_msg_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4229_: *mut LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0(v_00_u03b1_4222_, v_msg_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
    lean_dec(v___y_4227_);
    lean_dec_ref(v___y_4226_);
    lean_dec(v___y_4225_);
    lean_dec_ref(v___y_4224_);
    return v_res_4229_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(
    mut v_mvarId_4230_: *mut LeanObject,
    mut v_val_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    v___x_4237_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_mvarId_4230_, v_val_4231_, v___y_4233_);
    return v___x_4237_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___boxed(
    mut v_mvarId_4238_: *mut LeanObject,
    mut v_val_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4245_: *mut LeanObject = core::ptr::null_mut();
    v_res_4245_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1(v_mvarId_4238_, v_val_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
    lean_dec(v___y_4243_);
    lean_dec_ref(v___y_4242_);
    lean_dec(v___y_4241_);
    lean_dec_ref(v___y_4240_);
    return v_res_4245_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2(
    mut v_00_u03b2_4246_: *mut LeanObject,
    mut v_x_4247_: *mut LeanObject,
    mut v_x_4248_: *mut LeanObject,
    mut v_x_4249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2___redArg(v_x_4247_, v_x_4248_, v_x_4249_);
    return v___x_4250_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(
    mut v_00_u03b2_4251_: *mut LeanObject,
    mut v_x_4252_: *mut LeanObject,
    mut v_x_4253_: usize,
    mut v_x_4254_: usize,
    mut v_x_4255_: *mut LeanObject,
    mut v_x_4256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___redArg(v_x_4252_, v_x_4253_, v_x_4254_, v_x_4255_, v_x_4256_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_4258_: *mut LeanObject,
    mut v_x_4259_: *mut LeanObject,
    mut v_x_4260_: *mut LeanObject,
    mut v_x_4261_: *mut LeanObject,
    mut v_x_4262_: *mut LeanObject,
    mut v_x_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4870__boxed_4264_: usize = 0;
    let mut v_x_4871__boxed_4265_: usize = 0;
    let mut v_res_4266_: *mut LeanObject = core::ptr::null_mut();
    v_x_4870__boxed_4264_ = lean_unbox_usize(v_x_4260_);
    lean_dec(v_x_4260_);
    v_x_4871__boxed_4265_ = lean_unbox_usize(v_x_4261_);
    lean_dec(v_x_4261_);
    v_res_4266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3(v_00_u03b2_4258_, v_x_4259_, v_x_4870__boxed_4264_, v_x_4871__boxed_4265_, v_x_4262_, v_x_4263_);
    return v_res_4266_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_4267_: *mut LeanObject,
    mut v_n_4268_: *mut LeanObject,
    mut v_k_4269_: *mut LeanObject,
    mut v_v_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    v___x_4271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5___redArg(v_n_4268_, v_k_4269_, v_v_4270_);
    return v___x_4271_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(
    mut v_00_u03b2_4272_: *mut LeanObject,
    mut v_depth_4273_: usize,
    mut v_keys_4274_: *mut LeanObject,
    mut v_vals_4275_: *mut LeanObject,
    mut v_heq_4276_: *mut LeanObject,
    mut v_i_4277_: *mut LeanObject,
    mut v_entries_4278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    v___x_4279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___redArg(v_depth_4273_, v_keys_4274_, v_vals_4275_, v_i_4277_, v_entries_4278_);
    return v___x_4279_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_4280_: *mut LeanObject,
    mut v_depth_4281_: *mut LeanObject,
    mut v_keys_4282_: *mut LeanObject,
    mut v_vals_4283_: *mut LeanObject,
    mut v_heq_4284_: *mut LeanObject,
    mut v_i_4285_: *mut LeanObject,
    mut v_entries_4286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4287_: usize = 0;
    let mut v_res_4288_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4287_ = lean_unbox_usize(v_depth_4281_);
    lean_dec(v_depth_4281_);
    v_res_4288_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__6(v_00_u03b2_4280_, v_depth_boxed_4287_, v_keys_4282_, v_vals_4283_, v_heq_4284_, v_i_4285_, v_entries_4286_);
    lean_dec_ref(v_vals_4283_);
    lean_dec_ref(v_keys_4282_);
    return v_res_4288_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6(
    mut v_00_u03b2_4289_: *mut LeanObject,
    mut v_x_4290_: *mut LeanObject,
    mut v_x_4291_: *mut LeanObject,
    mut v_x_4292_: *mut LeanObject,
    mut v_x_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1_spec__2_spec__3_spec__5_spec__6___redArg(v_x_4290_, v_x_4291_, v_x_4292_, v_x_4293_);
    return v___x_4294_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(
    mut v_mvarId_4295_: *mut LeanObject,
    mut v_x_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4306_: u8 = 0;
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4302_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4295_,
                    v_x_4296_,
                    v___y_4297_,
                    v___y_4298_,
                    v___y_4299_,
                    v___y_4300_,
                );
                if lean_obj_tag(v___x_4302_) == 0 {
                    v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
                    v_isSharedCheck_4310_ = (!lean_is_exclusive(v___x_4302_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4305_ = v___x_4302_;
                        v_isShared_4306_ = v_isSharedCheck_4310_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4303_);
                        lean_dec(v___x_4302_);
                        v___x_4305_ = lean_box(0);
                        v_isShared_4306_ = v_isSharedCheck_4310_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4311_ = lean_ctor_get(v___x_4302_, 0);
                    v_isSharedCheck_4318_ = (!lean_is_exclusive(v___x_4302_)) as u8;
                    if v_isSharedCheck_4318_ == 0 {
                        v___x_4313_ = v___x_4302_;
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4311_);
                        lean_dec(v___x_4302_);
                        v___x_4313_ = lean_box(0);
                        v_isShared_4314_ = v_isSharedCheck_4318_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4306_ == 0 {
                    v___x_4308_ = v___x_4305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4309_, 0, v_a_4303_);
                    v___x_4308_ = v_reuseFailAlloc_4309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4308_;
            }
            3 => {
                if v_isShared_4314_ == 0 {
                    v___x_4316_ = v___x_4313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
                    v___x_4316_ = v_reuseFailAlloc_4317_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg___boxed(
    mut v_mvarId_4319_: *mut LeanObject,
    mut v_x_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4326_: *mut LeanObject = core::ptr::null_mut();
    v_res_4326_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_4319_, v_x_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_);
    lean_dec(v___y_4324_);
    lean_dec_ref(v___y_4323_);
    lean_dec(v___y_4322_);
    lean_dec_ref(v___y_4321_);
    return v_res_4326_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(
    mut v_00_u03b1_4327_: *mut LeanObject,
    mut v_mvarId_4328_: *mut LeanObject,
    mut v_x_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    v___x_4335_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_mvarId_4328_, v_x_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_);
    return v___x_4335_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___boxed(
    mut v_00_u03b1_4336_: *mut LeanObject,
    mut v_mvarId_4337_: *mut LeanObject,
    mut v_x_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4344_: *mut LeanObject = core::ptr::null_mut();
    v_res_4344_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0(v_00_u03b1_4336_, v_mvarId_4337_, v_x_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
    lean_dec(v___y_4342_);
    lean_dec_ref(v___y_4341_);
    lean_dec(v___y_4340_);
    lean_dec_ref(v___y_4339_);
    return v_res_4344_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    v___x_4348_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__1;
    v___x_4349_ = l_Lean_MessageData_ofFormat(v___x_4348_);
    return v___x_4349_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    v___x_4350_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__2);
    v___x_4351_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4351_, 0, v___x_4350_);
    return v___x_4351_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(
    mut v_goal_4356_: *mut LeanObject,
    mut v_name_4357_: *mut LeanObject,
    mut v_idx_4358_: *mut LeanObject,
    mut v_expected_x3f_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v_val_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4389_: u8 = 0;
    let mut v___y_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4424_: u8 = 0;
    let mut v_ctors_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: u8 = 0;
    let mut v___x_4428_: u8 = 0;
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4448_: u8 = 0;
    let mut v_reuseFailAlloc_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut v_isSharedCheck_4451_: u8 = 0;
    let mut v_isSharedCheck_4452_: u8 = 0;
    let mut v_a_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut v_a_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v___x_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_name_4357_);
                lean_inc(v_goal_4356_);
                v___x_4372_ = l_Lean_MVarId_checkNotAssigned(
                    v_goal_4356_,
                    v_name_4357_,
                    v___y_4360_,
                    v___y_4361_,
                    v___y_4362_,
                    v___y_4363_,
                );
                if lean_obj_tag(v___x_4372_) == 0 {
                    lean_dec_ref_known(v___x_4372_, 1);
                    lean_inc(v_goal_4356_);
                    v___x_4373_ = l_Lean_MVarId_getType_x27(
                        v_goal_4356_,
                        v___y_4360_,
                        v___y_4361_,
                        v___y_4362_,
                        v___y_4363_,
                    );
                    if lean_obj_tag(v___x_4373_) == 0 {
                        v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
                        lean_inc(v_a_4374_);
                        lean_dec_ref_known(v___x_4373_, 1);
                        v___x_4375_ = l_Lean_Expr_getAppFn(v_a_4374_);
                        lean_dec(v_a_4374_);
                        if lean_obj_tag(v___x_4375_) == 4 {
                            v_declName_4376_ = lean_ctor_get(v___x_4375_, 0);
                            lean_inc(v_declName_4376_);
                            v_us_4377_ = lean_ctor_get(v___x_4375_, 1);
                            lean_inc(v_us_4377_);
                            lean_dec_ref_known(v___x_4375_, 2);
                            v___x_4378_ = lean_st_ref_get(v___y_4363_);
                            v_env_4379_ = lean_ctor_get(v___x_4378_, 0);
                            lean_inc_ref(v_env_4379_);
                            lean_dec(v___x_4378_);
                            v___x_4380_ = 0;
                            v___x_4381_ = l_Lean_Environment_find_x3f(
                                v_env_4379_,
                                v_declName_4376_,
                                v___x_4380_,
                            );
                            if lean_obj_tag(v___x_4381_) == 0 {
                                lean_dec(v_us_4377_);
                                lean_dec(v_expected_x3f_4359_);
                                lean_dec(v_idx_4358_);
                                v___y_4366_ = v___y_4360_;
                                v___y_4367_ = v___y_4361_;
                                v___y_4368_ = v___y_4362_;
                                v___y_4369_ = v___y_4363_;
                                state = 1;
                                continue;
                            } else {
                                v_val_4382_ = lean_ctor_get(v___x_4381_, 0);
                                v_isSharedCheck_4452_ = (!lean_is_exclusive(v___x_4381_)) as u8;
                                if v_isSharedCheck_4452_ == 0 {
                                    v___x_4384_ = v___x_4381_;
                                    v_isShared_4385_ = v_isSharedCheck_4452_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_val_4382_);
                                    lean_dec(v___x_4381_);
                                    v___x_4384_ = lean_box(0);
                                    v_isShared_4385_ = v_isSharedCheck_4452_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4375_);
                            lean_dec(v_expected_x3f_4359_);
                            lean_dec(v_idx_4358_);
                            v___y_4366_ = v___y_4360_;
                            v___y_4367_ = v___y_4361_;
                            v___y_4368_ = v___y_4362_;
                            v___y_4369_ = v___y_4363_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_expected_x3f_4359_);
                        lean_dec(v_idx_4358_);
                        lean_dec(v_name_4357_);
                        lean_dec(v_goal_4356_);
                        v_a_4453_ = lean_ctor_get(v___x_4373_, 0);
                        v_isSharedCheck_4460_ = (!lean_is_exclusive(v___x_4373_)) as u8;
                        if v_isSharedCheck_4460_ == 0 {
                            v___x_4455_ = v___x_4373_;
                            v_isShared_4456_ = v_isSharedCheck_4460_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_4453_);
                            lean_dec(v___x_4373_);
                            v___x_4455_ = lean_box(0);
                            v_isShared_4456_ = v_isSharedCheck_4460_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_expected_x3f_4359_);
                    lean_dec(v_idx_4358_);
                    lean_dec(v_name_4357_);
                    lean_dec(v_goal_4356_);
                    v_a_4461_ = lean_ctor_get(v___x_4372_, 0);
                    v_isSharedCheck_4468_ = (!lean_is_exclusive(v___x_4372_)) as u8;
                    if v_isSharedCheck_4468_ == 0 {
                        v___x_4463_ = v___x_4372_;
                        v_isShared_4464_ = v_isSharedCheck_4468_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_4461_);
                        lean_dec(v___x_4372_);
                        v___x_4463_ = lean_box(0);
                        v_isShared_4464_ = v_isSharedCheck_4468_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4370_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__3);
                v___x_4371_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_4357_,
                    v_goal_4356_,
                    v___x_4370_,
                    v___y_4366_,
                    v___y_4367_,
                    v___y_4368_,
                    v___y_4369_,
                );
                return v___x_4371_;
            }
            2 => {
                if lean_obj_tag(v_val_4382_) == 5 {
                    v_val_4386_ = lean_ctor_get(v_val_4382_, 0);
                    v_isSharedCheck_4451_ = (!lean_is_exclusive(v_val_4382_)) as u8;
                    if v_isSharedCheck_4451_ == 0 {
                        v___x_4388_ = v_val_4382_;
                        v_isShared_4389_ = v_isSharedCheck_4451_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4386_);
                        lean_dec(v_val_4382_);
                        v___x_4388_ = lean_box(0);
                        v_isShared_4389_ = v_isSharedCheck_4451_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4384_);
                    lean_dec(v_val_4382_);
                    lean_dec(v_us_4377_);
                    lean_dec(v_expected_x3f_4359_);
                    lean_dec(v_idx_4358_);
                    v___y_4366_ = v___y_4360_;
                    v___y_4367_ = v___y_4361_;
                    v___y_4368_ = v___y_4362_;
                    v___y_4369_ = v___y_4363_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if lean_obj_tag(v_expected_x3f_4359_) == 1 {
                    v_val_4421_ = lean_ctor_get(v_expected_x3f_4359_, 0);
                    v_isSharedCheck_4450_ = (!lean_is_exclusive(v_expected_x3f_4359_)) as u8;
                    if v_isSharedCheck_4450_ == 0 {
                        v___x_4423_ = v_expected_x3f_4359_;
                        v_isShared_4424_ = v_isSharedCheck_4450_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_4421_);
                        lean_dec(v_expected_x3f_4359_);
                        v___x_4423_ = lean_box(0);
                        v_isShared_4424_ = v_isSharedCheck_4450_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v_expected_x3f_4359_);
                    v___y_4391_ = v___y_4360_;
                    v___y_4392_ = v___y_4361_;
                    v___y_4393_ = v___y_4362_;
                    v___y_4394_ = v___y_4363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_ctors_4395_ = lean_ctor_get(v_val_4386_, 4);
                lean_inc(v_ctors_4395_);
                lean_dec_ref(v_val_4386_);
                v___x_4396_ = l_List_lengthTR___redArg(v_ctors_4395_);
                v___x_4397_ = lean_nat_dec_lt(v_idx_4358_, v___x_4396_);
                if v___x_4397_ == 0 {
                    lean_dec(v_ctors_4395_);
                    lean_dec(v_us_4377_);
                    v___x_4398_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__4;
                    v___x_4399_ = l_Nat_reprFast(v_idx_4358_);
                    v___x_4400_ = lean_string_append(v___x_4398_, v___x_4399_);
                    lean_dec_ref(v___x_4399_);
                    v___x_4401_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__5;
                    v___x_4402_ = lean_string_append(v___x_4400_, v___x_4401_);
                    v___x_4403_ = l_Nat_reprFast(v___x_4396_);
                    v___x_4404_ = lean_string_append(v___x_4402_, v___x_4403_);
                    lean_dec_ref(v___x_4403_);
                    v___x_4405_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_4406_ = lean_string_append(v___x_4404_, v___x_4405_);
                    if v_isShared_4389_ == 0 {
                        lean_ctor_set_tag(v___x_4388_, 3);
                        lean_ctor_set(v___x_4388_, 0, v___x_4406_);
                        v___x_4408_ = v___x_4388_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4406_);
                        v___x_4408_ = v_reuseFailAlloc_4414_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4396_);
                    lean_del_object(v___x_4388_);
                    lean_del_object(v___x_4384_);
                    lean_dec(v_name_4357_);
                    v___x_4415_ = l_List_get___redArg(v_ctors_4395_, v_idx_4358_);
                    lean_dec(v_ctors_4395_);
                    v___x_4416_ = l_Lean_mkConst(v___x_4415_, v_us_4377_);
                    v___x_4417_ = 0;
                    v___x_4418_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v___x_4418_, 0 as u32, v___x_4417_);
                    lean_ctor_set_uint8(v___x_4418_, 1 as u32, v___x_4397_);
                    lean_ctor_set_uint8(v___x_4418_, 2 as u32, v___x_4380_);
                    lean_ctor_set_uint8(v___x_4418_, 3 as u32, v___x_4397_);
                    v___x_4419_ = lean_box(0);
                    v___x_4420_ = l_Lean_MVarId_apply(
                        v_goal_4356_,
                        v___x_4416_,
                        v___x_4418_,
                        v___x_4419_,
                        v___y_4391_,
                        v___y_4392_,
                        v___y_4393_,
                        v___y_4394_,
                    );
                    return v___x_4420_;
                }
            }
            5 => {
                v___x_4409_ = l_Lean_MessageData_ofFormat(v___x_4408_);
                if v_isShared_4385_ == 0 {
                    lean_ctor_set(v___x_4384_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4384_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4413_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4412_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_4357_,
                    v_goal_4356_,
                    v___x_4411_,
                    v___y_4391_,
                    v___y_4392_,
                    v___y_4393_,
                    v___y_4394_,
                );
                return v___x_4412_;
            }
            7 => {
                v_ctors_4425_ = lean_ctor_get(v_val_4386_, 4);
                v___x_4426_ = l_List_lengthTR___redArg(v_ctors_4425_);
                v___x_4427_ = lean_nat_dec_eq(v___x_4426_, v_val_4421_);
                lean_dec(v___x_4426_);
                if v___x_4427_ == 0 {
                    v___x_4428_ = 1;
                    lean_inc(v_name_4357_);
                    v___x_4429_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_4357_,
                        v___x_4428_,
                    );
                    v___x_4430_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__7;
                    v___x_4431_ = lean_string_append(v___x_4429_, v___x_4430_);
                    v___x_4432_ = l_Nat_reprFast(v_val_4421_);
                    v___x_4433_ = lean_string_append(v___x_4431_, v___x_4432_);
                    lean_dec_ref(v___x_4432_);
                    v___x_4434_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_4435_ = lean_string_append(v___x_4433_, v___x_4434_);
                    v___x_4436_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_4436_, 0, v___x_4435_);
                    v___x_4437_ = l_Lean_MessageData_ofFormat(v___x_4436_);
                    if v_isShared_4424_ == 0 {
                        lean_ctor_set(v___x_4423_, 0, v___x_4437_);
                        v___x_4439_ = v___x_4423_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4437_);
                        v___x_4439_ = v_reuseFailAlloc_4449_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4423_);
                    lean_dec(v_val_4421_);
                    v___y_4391_ = v___y_4360_;
                    v___y_4392_ = v___y_4361_;
                    v___y_4393_ = v___y_4362_;
                    v___y_4394_ = v___y_4363_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                lean_inc(v_goal_4356_);
                lean_inc(v_name_4357_);
                v___x_4440_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_4357_,
                    v_goal_4356_,
                    v___x_4439_,
                    v___y_4360_,
                    v___y_4361_,
                    v___y_4362_,
                    v___y_4363_,
                );
                if lean_obj_tag(v___x_4440_) == 0 {
                    lean_dec_ref_known(v___x_4440_, 1);
                    v___y_4391_ = v___y_4360_;
                    v___y_4392_ = v___y_4361_;
                    v___y_4393_ = v___y_4362_;
                    v___y_4394_ = v___y_4363_;
                    state = 4;
                    continue;
                } else {
                    lean_del_object(v___x_4388_);
                    lean_dec_ref(v_val_4386_);
                    lean_del_object(v___x_4384_);
                    lean_dec(v_us_4377_);
                    lean_dec(v_idx_4358_);
                    lean_dec(v_name_4357_);
                    lean_dec(v_goal_4356_);
                    v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
                    v_isSharedCheck_4448_ = (!lean_is_exclusive(v___x_4440_)) as u8;
                    if v_isSharedCheck_4448_ == 0 {
                        v___x_4443_ = v___x_4440_;
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4441_);
                        lean_dec(v___x_4440_);
                        v___x_4443_ = lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4444_ == 0 {
                    v___x_4446_ = v___x_4443_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
                    v___x_4446_ = v_reuseFailAlloc_4447_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4446_;
            }
            11 => {
                if v_isShared_4456_ == 0 {
                    v___x_4458_ = v___x_4455_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
                    v___x_4458_ = v_reuseFailAlloc_4459_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4458_;
            }
            13 => {
                if v_isShared_4464_ == 0 {
                    v___x_4466_ = v___x_4463_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
                    v___x_4466_ = v_reuseFailAlloc_4467_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed(
    mut v_goal_4469_: *mut LeanObject,
    mut v_name_4470_: *mut LeanObject,
    mut v_idx_4471_: *mut LeanObject,
    mut v_expected_x3f_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4478_: *mut LeanObject = core::ptr::null_mut();
    v_res_4478_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0(
            v_goal_4469_,
            v_name_4470_,
            v_idx_4471_,
            v_expected_x3f_4472_,
            v___y_4473_,
            v___y_4474_,
            v___y_4475_,
            v___y_4476_,
        );
    lean_dec(v___y_4476_);
    lean_dec_ref(v___y_4475_);
    lean_dec(v___y_4474_);
    lean_dec_ref(v___y_4473_);
    return v_res_4478_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(
    mut v_name_4479_: *mut LeanObject,
    mut v_idx_4480_: *mut LeanObject,
    mut v_expected_x3f_4481_: *mut LeanObject,
    mut v_goal_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_a_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v_a_4486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_4482_);
    v___f_4488_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___lam__0___boxed as *mut core::ffi::c_void, 9, 4);
    lean_closure_set(v___f_4488_, 0, v_goal_4482_);
    lean_closure_set(v___f_4488_, 1, v_name_4479_);
    lean_closure_set(v___f_4488_, 2, v_idx_4480_);
    lean_closure_set(v___f_4488_, 3, v_expected_x3f_4481_);
    v___x_4489_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_goal_4482_, v___f_4488_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
    return v___x_4489_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor___boxed(
    mut v_name_4490_: *mut LeanObject,
    mut v_idx_4491_: *mut LeanObject,
    mut v_expected_x3f_4492_: *mut LeanObject,
    mut v_goal_4493_: *mut LeanObject,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
    mut v_a_4497_: *mut LeanObject,
    mut v_a_4498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4499_: *mut LeanObject = core::ptr::null_mut();
    v_res_4499_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(
        v_name_4490_,
        v_idx_4491_,
        v_expected_x3f_4492_,
        v_goal_4493_,
        v_a_4494_,
        v_a_4495_,
        v_a_4496_,
        v_a_4497_,
    );
    lean_dec(v_a_4497_);
    lean_dec_ref(v_a_4496_);
    lean_dec(v_a_4495_);
    lean_dec_ref(v_a_4494_);
    return v_res_4499_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4()
-> *mut LeanObject {
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4506_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__3;
    v___x_4507_ = l_Lean_stringToMessageData(v___x_4506_);
    return v___x_4507_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8()
-> *mut LeanObject {
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    v___x_4512_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__7;
    v___x_4513_ = l_Lean_stringToMessageData(v___x_4512_);
    return v___x_4513_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(
    mut v_m_4514_: *mut LeanObject,
    mut v_n_4515_: *mut LeanObject,
    mut v_goal_4516_: *mut LeanObject,
    mut v_a_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_4523_: u8 = 0;
    let mut v_isZero_4524_: u8 = 0;
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4532_: u8 = 0;
    let mut v___y_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v_a_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4553_: u8 = 0;
    let mut v_isZero_4554_: u8 = 0;
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4575_: u8 = 0;
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4522_ = lean_unsigned_to_nat(0);
                v_isZero_4523_ = lean_nat_dec_eq(v_m_4514_, v_zero_4522_);
                if v_isZero_4523_ == 1 {
                    lean_dec(v_m_4514_);
                    v_isZero_4524_ = lean_nat_dec_eq(v_n_4515_, v_zero_4522_);
                    lean_dec(v_n_4515_);
                    if v_isZero_4524_ == 1 {
                        v___x_4525_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4525_, 0, v_goal_4516_);
                        return v___x_4525_;
                    } else {
                        v___x_4526_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__1;
                        v___x_4527_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2;
                        v___x_4528_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_4526_, v_zero_4522_, v___x_4527_, v_goal_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
                        if lean_obj_tag(v___x_4528_) == 0 {
                            v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
                            v_isSharedCheck_4545_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                            if v_isSharedCheck_4545_ == 0 {
                                v___x_4531_ = v___x_4528_;
                                v_isShared_4532_ = v_isSharedCheck_4545_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4529_);
                                lean_dec(v___x_4528_);
                                v___x_4531_ = lean_box(0);
                                v_isShared_4532_ = v_isSharedCheck_4545_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4546_ = lean_ctor_get(v___x_4528_, 0);
                            v_isSharedCheck_4553_ = (!lean_is_exclusive(v___x_4528_)) as u8;
                            if v_isSharedCheck_4553_ == 0 {
                                v___x_4548_ = v___x_4528_;
                                v_isShared_4549_ = v_isSharedCheck_4553_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4546_);
                                lean_dec(v___x_4528_);
                                v___x_4548_ = lean_box(0);
                                v_isShared_4549_ = v_isSharedCheck_4553_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    v_isZero_4554_ = lean_nat_dec_eq(v_n_4515_, v_zero_4522_);
                    if v_isZero_4554_ == 0 {
                        v___x_4555_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__6;
                        v___x_4556_ = lean_unsigned_to_nat(1);
                        v___x_4557_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__2;
                        v___x_4558_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor(v___x_4555_, v___x_4556_, v___x_4557_, v_goal_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
                        if lean_obj_tag(v___x_4558_) == 0 {
                            v_a_4559_ = lean_ctor_get(v___x_4558_, 0);
                            lean_inc(v_a_4559_);
                            lean_dec_ref_known(v___x_4558_, 1);
                            if lean_obj_tag(v_a_4559_) == 1 {
                                v_tail_4567_ = lean_ctor_get(v_a_4559_, 1);
                                if lean_obj_tag(v_tail_4567_) == 0 {
                                    v_head_4568_ = lean_ctor_get(v_a_4559_, 0);
                                    lean_inc(v_head_4568_);
                                    lean_dec_ref_known(v_a_4559_, 2);
                                    v_n_4569_ = lean_nat_sub(v_m_4514_, v___x_4556_);
                                    lean_dec(v_m_4514_);
                                    v_n_4570_ = lean_nat_sub(v_n_4515_, v___x_4556_);
                                    lean_dec(v_n_4515_);
                                    v_m_4514_ = v_n_4569_;
                                    v_n_4515_ = v_n_4570_;
                                    v_goal_4516_ = v_head_4568_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref_known(v_a_4559_, 2);
                                    lean_dec(v_n_4515_);
                                    lean_dec(v_m_4514_);
                                    v___y_4561_ = v_a_4517_;
                                    v___y_4562_ = v_a_4518_;
                                    v___y_4563_ = v_a_4519_;
                                    v___y_4564_ = v_a_4520_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4559_);
                                lean_dec(v_n_4515_);
                                lean_dec(v_m_4514_);
                                v___y_4561_ = v_a_4517_;
                                v___y_4562_ = v_a_4518_;
                                v___y_4563_ = v_a_4519_;
                                v___y_4564_ = v_a_4520_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_n_4515_);
                            lean_dec(v_m_4514_);
                            v_a_4572_ = lean_ctor_get(v___x_4558_, 0);
                            v_isSharedCheck_4579_ = (!lean_is_exclusive(v___x_4558_)) as u8;
                            if v_isSharedCheck_4579_ == 0 {
                                v___x_4574_ = v___x_4558_;
                                v_isShared_4575_ = v_isSharedCheck_4579_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4572_);
                                lean_dec(v___x_4558_);
                                v___x_4574_ = lean_box(0);
                                v_isShared_4575_ = v_isSharedCheck_4579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_goal_4516_);
                        lean_dec(v_n_4515_);
                        lean_dec(v_m_4514_);
                        v___x_4580_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__8);
                        v___x_4581_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_4580_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_);
                        return v___x_4581_;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4529_) == 1 {
                    v_tail_4540_ = lean_ctor_get(v_a_4529_, 1);
                    if lean_obj_tag(v_tail_4540_) == 0 {
                        v_head_4541_ = lean_ctor_get(v_a_4529_, 0);
                        lean_inc(v_head_4541_);
                        lean_dec_ref_known(v_a_4529_, 2);
                        if v_isShared_4532_ == 0 {
                            lean_ctor_set(v___x_4531_, 0, v_head_4541_);
                            v___x_4543_ = v___x_4531_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_head_4541_);
                            v___x_4543_ = v_reuseFailAlloc_4544_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_4529_, 2);
                        lean_del_object(v___x_4531_);
                        v___y_4534_ = v_a_4517_;
                        v___y_4535_ = v_a_4518_;
                        v___y_4536_ = v_a_4519_;
                        v___y_4537_ = v_a_4520_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4531_);
                    lean_dec(v_a_4529_);
                    v___y_4534_ = v_a_4517_;
                    v___y_4535_ = v_a_4518_;
                    v___y_4536_ = v_a_4519_;
                    v___y_4537_ = v_a_4520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4538_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4);
                v___x_4539_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_4538_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                return v___x_4539_;
            }
            3 => {
                return v___x_4543_;
            }
            4 => {
                if v_isShared_4549_ == 0 {
                    v___x_4551_ = v___x_4548_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
                    v___x_4551_ = v_reuseFailAlloc_4552_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4551_;
            }
            6 => {
                v___x_4565_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___closed__4);
                v___x_4566_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_4565_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
                return v___x_4566_;
            }
            7 => {
                if v_isShared_4575_ == 0 {
                    v___x_4577_ = v___x_4574_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
                    v___x_4577_ = v_reuseFailAlloc_4578_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select___boxed(
    mut v_m_4582_: *mut LeanObject,
    mut v_n_4583_: *mut LeanObject,
    mut v_goal_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4590_: *mut LeanObject = core::ptr::null_mut();
    v_res_4590_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(
        v_m_4582_,
        v_n_4583_,
        v_goal_4584_,
        v_a_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
    );
    lean_dec(v_a_4588_);
    lean_dec_ref(v_a_4587_);
    lean_dec(v_a_4586_);
    lean_dec_ref(v_a_4585_);
    return v_res_4590_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(
    mut v___y_4591_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_4591_);
    return v___y_4591_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0___boxed(
    mut v___y_4592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4593_: *mut LeanObject = core::ptr::null_mut();
    v_res_4593_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__0(
        v___y_4592_,
    );
    lean_dec_ref(v___y_4592_);
    return v_res_4593_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(
    mut v_snd_4594_: *mut LeanObject,
    mut v_head_4595_: *mut LeanObject,
    mut v_fst_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    v___x_4598_ = lean_apply_1(v_snd_4594_, v___y_4597_);
    v___x_4599_ = l_Lean_Expr_replaceFVar(v___x_4598_, v_head_4595_, v_fst_4596_);
    lean_dec_ref(v___x_4598_);
    return v___x_4599_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed(
    mut v_snd_4600_: *mut LeanObject,
    mut v_head_4601_: *mut LeanObject,
    mut v_fst_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4604_: *mut LeanObject = core::ptr::null_mut();
    v_res_4604_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1(
        v_snd_4600_,
        v_head_4601_,
        v_fst_4602_,
        v___y_4603_,
    );
    lean_dec_ref(v_fst_4602_);
    return v_res_4604_;
}
pub unsafe fn l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(
    mut v_head_4605_: *mut LeanObject,
    mut v_a_4606_: *mut LeanObject,
    mut v_a_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: u8 = 0;
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_unused_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4631_: u8 = 0;
    let mut v_unused_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4606_) == 0 {
                    v___x_4608_ = l_List_reverse___redArg(v_a_4607_);
                    v___x_4609_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4609_, 0, v___x_4608_);
                    lean_ctor_set(v___x_4609_, 1, v_a_4606_);
                    return v___x_4609_;
                } else {
                    v_head_4610_ = lean_ctor_get(v_a_4606_, 0);
                    lean_inc(v_head_4610_);
                    v_tail_4611_ = lean_ctor_get(v_a_4606_, 1);
                    v_snd_4612_ = lean_ctor_get(v_head_4610_, 1);
                    v___x_4613_ = lean_expr_eqv(v_snd_4612_, v_head_4605_);
                    if v___x_4613_ == 0 {
                        lean_inc(v_tail_4611_);
                        v_isSharedCheck_4621_ = (!lean_is_exclusive(v_a_4606_)) as u8;
                        if v_isSharedCheck_4621_ == 0 {
                            v_unused_4622_ = lean_ctor_get(v_a_4606_, 1);
                            lean_dec(v_unused_4622_);
                            v_unused_4623_ = lean_ctor_get(v_a_4606_, 0);
                            lean_dec(v_unused_4623_);
                            v___x_4615_ = v_a_4606_;
                            v_isShared_4616_ = v_isSharedCheck_4621_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_4606_);
                            v___x_4615_ = lean_box(0);
                            v_isShared_4616_ = v_isSharedCheck_4621_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_4631_ = (!lean_is_exclusive(v_head_4610_)) as u8;
                        if v_isSharedCheck_4631_ == 0 {
                            v_unused_4632_ = lean_ctor_get(v_head_4610_, 1);
                            lean_dec(v_unused_4632_);
                            v_unused_4633_ = lean_ctor_get(v_head_4610_, 0);
                            lean_dec(v_unused_4633_);
                            v___x_4625_ = v_head_4610_;
                            v_isShared_4626_ = v_isSharedCheck_4631_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_head_4610_);
                            v___x_4625_ = lean_box(0);
                            v_isShared_4626_ = v_isSharedCheck_4631_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4616_ == 0 {
                    lean_ctor_set(v___x_4615_, 1, v_a_4607_);
                    v___x_4618_ = v___x_4615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_head_4610_);
                    lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_a_4607_);
                    v___x_4618_ = v_reuseFailAlloc_4620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4606_ = v_tail_4611_;
                v_a_4607_ = v___x_4618_;
                state = 0;
                continue;
            }
            3 => {
                v___x_4627_ = l_List_reverse___redArg(v_a_4607_);
                if v_isShared_4626_ == 0 {
                    lean_ctor_set(v___x_4625_, 1, v_a_4606_);
                    lean_ctor_set(v___x_4625_, 0, v___x_4627_);
                    v___x_4629_ = v___x_4625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4627_);
                    lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_a_4606_);
                    v___x_4629_ = v_reuseFailAlloc_4630_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0___boxed(
    mut v_head_4634_: *mut LeanObject,
    mut v_a_4635_: *mut LeanObject,
    mut v_a_4636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4637_: *mut LeanObject = core::ptr::null_mut();
    v_res_4637_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_4634_, v_a_4635_, v_a_4636_);
    lean_dec_ref(v_head_4634_);
    return v_res_4637_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(
    mut v_head_4638_: *mut LeanObject,
    mut v_fst_4639_: *mut LeanObject,
    mut v_a_4640_: *mut LeanObject,
    mut v_a_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v_fst_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4661_: u8 = 0;
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4640_) == 0 {
                    lean_dec_ref(v_head_4638_);
                    v___x_4642_ = l_List_reverse___redArg(v_a_4641_);
                    return v___x_4642_;
                } else {
                    v_head_4643_ = lean_ctor_get(v_a_4640_, 0);
                    v_tail_4644_ = lean_ctor_get(v_a_4640_, 1);
                    v_isSharedCheck_4662_ = (!lean_is_exclusive(v_a_4640_)) as u8;
                    if v_isSharedCheck_4662_ == 0 {
                        v___x_4646_ = v_a_4640_;
                        v_isShared_4647_ = v_isSharedCheck_4662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4644_);
                        lean_inc(v_head_4643_);
                        lean_dec(v_a_4640_);
                        v___x_4646_ = lean_box(0);
                        v_isShared_4647_ = v_isSharedCheck_4662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4648_ = lean_ctor_get(v_head_4643_, 0);
                v_snd_4649_ = lean_ctor_get(v_head_4643_, 1);
                v_isSharedCheck_4661_ = (!lean_is_exclusive(v_head_4643_)) as u8;
                if v_isSharedCheck_4661_ == 0 {
                    v___x_4651_ = v_head_4643_;
                    v_isShared_4652_ = v_isSharedCheck_4661_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_4649_);
                    lean_inc(v_fst_4648_);
                    lean_dec(v_head_4643_);
                    v___x_4651_ = lean_box(0);
                    v_isShared_4652_ = v_isSharedCheck_4661_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_head_4638_);
                v___x_4653_ = l_Lean_Expr_replaceFVar(v_snd_4649_, v_head_4638_, v_fst_4639_);
                lean_dec(v_snd_4649_);
                if v_isShared_4652_ == 0 {
                    lean_ctor_set(v___x_4651_, 1, v___x_4653_);
                    v___x_4655_ = v___x_4651_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4660_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4660_, 0, v_fst_4648_);
                    lean_ctor_set(v_reuseFailAlloc_4660_, 1, v___x_4653_);
                    v___x_4655_ = v_reuseFailAlloc_4660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4647_ == 0 {
                    lean_ctor_set(v___x_4646_, 1, v_a_4641_);
                    lean_ctor_set(v___x_4646_, 0, v___x_4655_);
                    v___x_4657_ = v___x_4646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4655_);
                    lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_a_4641_);
                    v___x_4657_ = v_reuseFailAlloc_4659_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_4640_ = v_tail_4644_;
                v_a_4641_ = v___x_4657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2___boxed(
    mut v_head_4663_: *mut LeanObject,
    mut v_fst_4664_: *mut LeanObject,
    mut v_a_4665_: *mut LeanObject,
    mut v_a_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4667_: *mut LeanObject = core::ptr::null_mut();
    v_res_4667_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_4663_, v_fst_4664_, v_a_4665_, v_a_4666_);
    lean_dec_ref(v_fst_4664_);
    return v_res_4667_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(
    mut v_head_4668_: *mut LeanObject,
    mut v_fst_4669_: *mut LeanObject,
    mut v_a_4670_: *mut LeanObject,
    mut v_a_4671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4677_: u8 = 0;
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4670_) == 0 {
                    lean_dec_ref(v_head_4668_);
                    v___x_4672_ = l_List_reverse___redArg(v_a_4671_);
                    return v___x_4672_;
                } else {
                    v_head_4673_ = lean_ctor_get(v_a_4670_, 0);
                    v_tail_4674_ = lean_ctor_get(v_a_4670_, 1);
                    v_isSharedCheck_4683_ = (!lean_is_exclusive(v_a_4670_)) as u8;
                    if v_isSharedCheck_4683_ == 0 {
                        v___x_4676_ = v_a_4670_;
                        v_isShared_4677_ = v_isSharedCheck_4683_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4674_);
                        lean_inc(v_head_4673_);
                        lean_dec(v_a_4670_);
                        v___x_4676_ = lean_box(0);
                        v_isShared_4677_ = v_isSharedCheck_4683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_head_4668_);
                v___x_4678_ = l_Lean_Expr_replaceFVar(v_head_4673_, v_head_4668_, v_fst_4669_);
                lean_dec(v_head_4673_);
                if v_isShared_4677_ == 0 {
                    lean_ctor_set(v___x_4676_, 1, v_a_4671_);
                    lean_ctor_set(v___x_4676_, 0, v___x_4678_);
                    v___x_4680_ = v___x_4676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4682_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4682_, 0, v___x_4678_);
                    lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_a_4671_);
                    v___x_4680_ = v_reuseFailAlloc_4682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4670_ = v_tail_4674_;
                v_a_4671_ = v___x_4680_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1___boxed(
    mut v_head_4684_: *mut LeanObject,
    mut v_fst_4685_: *mut LeanObject,
    mut v_a_4686_: *mut LeanObject,
    mut v_a_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4688_: *mut LeanObject = core::ptr::null_mut();
    v_res_4688_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_4684_, v_fst_4685_, v_a_4686_, v_a_4687_);
    lean_dec_ref(v_fst_4685_);
    return v_res_4688_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(
    mut v_x_4690_: *mut LeanObject,
    mut v_x_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4709_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4717_: u8 = 0;
    let mut v_head_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4723_: u8 = 0;
    let mut v_fst_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v_fst_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4738_: u8 = 0;
    let mut v___f_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_unused_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4690_) == 0 {
                    v___f_4692_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___closed__0;
                    v___x_4693_ = lean_box(0);
                    v___x_4694_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4694_, 0, v_x_4691_);
                    lean_ctor_set(v___x_4694_, 1, v___f_4692_);
                    v___x_4695_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4695_, 0, v___x_4693_);
                    lean_ctor_set(v___x_4695_, 1, v___x_4694_);
                    return v___x_4695_;
                } else {
                    v_head_4696_ = lean_ctor_get(v_x_4690_, 0);
                    v_tail_4697_ = lean_ctor_get(v_x_4690_, 1);
                    v_isSharedCheck_4754_ = (!lean_is_exclusive(v_x_4690_)) as u8;
                    if v_isSharedCheck_4754_ == 0 {
                        v___x_4699_ = v_x_4690_;
                        v_isShared_4700_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4697_);
                        lean_inc(v_head_4696_);
                        lean_dec(v_x_4690_);
                        v___x_4699_ = lean_box(0);
                        v_isShared_4700_ = v_isSharedCheck_4754_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4701_ = lean_box(0);
                lean_inc(v_x_4691_);
                v___x_4702_ = l_List_span_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__0(v_head_4696_, v_x_4691_, v___x_4701_);
                v_snd_4703_ = lean_ctor_get(v___x_4702_, 1);
                lean_inc(v_snd_4703_);
                if lean_obj_tag(v_snd_4703_) == 0 {
                    lean_dec_ref(v___x_4702_);
                    v___x_4704_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(
                            v_tail_4697_,
                            v_x_4691_,
                        );
                    v_fst_4705_ = lean_ctor_get(v___x_4704_, 0);
                    v_snd_4706_ = lean_ctor_get(v___x_4704_, 1);
                    v_isSharedCheck_4717_ = (!lean_is_exclusive(v___x_4704_)) as u8;
                    if v_isSharedCheck_4717_ == 0 {
                        v___x_4708_ = v___x_4704_;
                        v_isShared_4709_ = v_isSharedCheck_4717_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4706_);
                        lean_inc(v_fst_4705_);
                        lean_dec(v___x_4704_);
                        v___x_4708_ = lean_box(0);
                        v_isShared_4709_ = v_isSharedCheck_4717_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4699_);
                    lean_dec(v_x_4691_);
                    v_head_4718_ = lean_ctor_get(v_snd_4703_, 0);
                    lean_inc(v_head_4718_);
                    v_fst_4719_ = lean_ctor_get(v___x_4702_, 0);
                    lean_inc(v_fst_4719_);
                    lean_dec_ref(v___x_4702_);
                    v_tail_4720_ = lean_ctor_get(v_snd_4703_, 1);
                    v_isSharedCheck_4752_ = (!lean_is_exclusive(v_snd_4703_)) as u8;
                    if v_isSharedCheck_4752_ == 0 {
                        v_unused_4753_ = lean_ctor_get(v_snd_4703_, 0);
                        lean_dec(v_unused_4753_);
                        v___x_4722_ = v_snd_4703_;
                        v_isShared_4723_ = v_isSharedCheck_4752_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_tail_4720_);
                        lean_dec(v_snd_4703_);
                        v___x_4722_ = lean_box(0);
                        v_isShared_4723_ = v_isSharedCheck_4752_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4710_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4710_, 0, v_head_4696_);
                if v_isShared_4700_ == 0 {
                    lean_ctor_set(v___x_4699_, 1, v_fst_4705_);
                    lean_ctor_set(v___x_4699_, 0, v___x_4710_);
                    v___x_4712_ = v___x_4699_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4710_);
                    lean_ctor_set(v_reuseFailAlloc_4716_, 1, v_fst_4705_);
                    v___x_4712_ = v_reuseFailAlloc_4716_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4709_ == 0 {
                    lean_ctor_set(v___x_4708_, 0, v___x_4712_);
                    v___x_4714_ = v___x_4708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4715_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
                    lean_ctor_set(v_reuseFailAlloc_4715_, 1, v_snd_4706_);
                    v___x_4714_ = v_reuseFailAlloc_4715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4714_;
            }
            5 => {
                v_fst_4724_ = lean_ctor_get(v_head_4718_, 0);
                lean_inc(v_fst_4724_);
                lean_dec(v_head_4718_);
                lean_inc_n(v_head_4696_, 2);
                v___x_4725_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__1(v_head_4696_, v_fst_4724_, v_tail_4697_, v___x_4701_);
                v___x_4726_ = l_List_appendTR___redArg(v_fst_4719_, v_tail_4720_);
                v___x_4727_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation_spec__2(v_head_4696_, v_fst_4724_, v___x_4726_, v___x_4701_);
                v___x_4728_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(
                        v___x_4725_,
                        v___x_4727_,
                    );
                v_snd_4729_ = lean_ctor_get(v___x_4728_, 1);
                v_fst_4730_ = lean_ctor_get(v___x_4728_, 0);
                v_isSharedCheck_4751_ = (!lean_is_exclusive(v___x_4728_)) as u8;
                if v_isSharedCheck_4751_ == 0 {
                    v___x_4732_ = v___x_4728_;
                    v_isShared_4733_ = v_isSharedCheck_4751_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_4729_);
                    lean_inc(v_fst_4730_);
                    lean_dec(v___x_4728_);
                    v___x_4732_ = lean_box(0);
                    v_isShared_4733_ = v_isSharedCheck_4751_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_fst_4734_ = lean_ctor_get(v_snd_4729_, 0);
                v_snd_4735_ = lean_ctor_get(v_snd_4729_, 1);
                v_isSharedCheck_4750_ = (!lean_is_exclusive(v_snd_4729_)) as u8;
                if v_isSharedCheck_4750_ == 0 {
                    v___x_4737_ = v_snd_4729_;
                    v_isShared_4738_ = v_isSharedCheck_4750_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_4735_);
                    lean_inc(v_fst_4734_);
                    lean_dec(v_snd_4729_);
                    v___x_4737_ = lean_box(0);
                    v_isShared_4738_ = v_isSharedCheck_4750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___f_4739_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___f_4739_, 0, v_snd_4735_);
                lean_closure_set(v___f_4739_, 1, v_head_4696_);
                lean_closure_set(v___f_4739_, 2, v_fst_4724_);
                v___x_4740_ = lean_box(0);
                if v_isShared_4723_ == 0 {
                    lean_ctor_set(v___x_4722_, 1, v_fst_4730_);
                    lean_ctor_set(v___x_4722_, 0, v___x_4740_);
                    v___x_4742_ = v___x_4722_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 0, v___x_4740_);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 1, v_fst_4730_);
                    v___x_4742_ = v_reuseFailAlloc_4749_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4738_ == 0 {
                    lean_ctor_set(v___x_4737_, 1, v___f_4739_);
                    v___x_4744_ = v___x_4737_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_fst_4734_);
                    lean_ctor_set(v_reuseFailAlloc_4748_, 1, v___f_4739_);
                    v___x_4744_ = v_reuseFailAlloc_4748_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4733_ == 0 {
                    lean_ctor_set(v___x_4732_, 1, v___x_4744_);
                    lean_ctor_set(v___x_4732_, 0, v___x_4742_);
                    v___x_4746_ = v___x_4732_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4747_, 0, v___x_4742_);
                    lean_ctor_set(v_reuseFailAlloc_4747_, 1, v___x_4744_);
                    v___x_4746_ = v_reuseFailAlloc_4747_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4746_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(
    mut v_msg_4755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    v___x_4756_ = l_Lean_instInhabitedExpr;
    v___x_4757_ = lean_panic_fn_borrowed(v___x_4756_, v_msg_4755_);
    return v___x_4757_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3()
-> *mut LeanObject {
    let mut v___x_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    v___x_4761_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__2;
    v___x_4762_ = lean_unsigned_to_nat(19);
    v___x_4763_ = lean_unsigned_to_nat(96);
    v___x_4764_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__1;
    v___x_4765_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__0;
    v___x_4766_ = l_mkPanicMessageWithDecl(
        v___x_4765_,
        v___x_4764_,
        v___x_4763_,
        v___x_4762_,
        v___x_4761_,
    );
    return v___x_4766_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(
    mut v_e_4767_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_4767_) == 6 {
        let mut v_binderName_4768_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_4769_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_4770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4771_: u8 = 0;
        let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
        v_binderName_4768_ = lean_ctor_get(v_e_4767_, 0);
        lean_inc(v_binderName_4768_);
        v_binderType_4769_ = lean_ctor_get(v_e_4767_, 1);
        lean_inc_ref(v_binderType_4769_);
        v_body_4770_ = lean_ctor_get(v_e_4767_, 2);
        lean_inc_ref(v_body_4770_);
        lean_dec_ref_known(v_e_4767_, 3);
        v___x_4771_ = 0;
        v___x_4772_ = l_Lean_Expr_lam___override(
            v_binderName_4768_,
            v_binderType_4769_,
            v_body_4770_,
            v___x_4771_,
        );
        return v___x_4772_;
    } else {
        let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_4767_);
        v___x_4773_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21___closed__3);
        v___x_4774_ = l_panic___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21_spec__0(v___x_4773_);
        return v___x_4774_;
    }
}
pub unsafe fn _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    v___x_4781_ = lean_box(0);
    v___x_4782_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__3;
    v___x_4783_ = l_Lean_mkConst(v___x_4782_, v___x_4781_);
    return v___x_4783_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(
    mut v_x_4784_: *mut LeanObject,
    mut v_x_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___y_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: u8 = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4825_: u8 = 0;
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: u8 = 0;
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: u8 = 0;
    let mut v_isSharedCheck_4832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4785_) == 0 {
                    v___x_4791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4791_, 0, v_x_4784_);
                    return v___x_4791_;
                } else {
                    v_head_4792_ = lean_ctor_get(v_x_4785_, 0);
                    v_tail_4793_ = lean_ctor_get(v_x_4785_, 1);
                    v_isSharedCheck_4832_ = (!lean_is_exclusive(v_x_4785_)) as u8;
                    if v_isSharedCheck_4832_ == 0 {
                        v___x_4795_ = v_x_4785_;
                        v_isShared_4796_ = v_isSharedCheck_4832_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4793_);
                        lean_inc(v_head_4792_);
                        lean_dec(v_x_4785_);
                        v___x_4795_ = lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4832_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_4789_);
                lean_inc_ref(v___y_4788_);
                lean_inc(v___y_4787_);
                lean_inc_ref(v___y_4786_);
                lean_inc(v_head_4792_);
                v___x_4801_ = lean_infer_type(
                    v_head_4792_,
                    v___y_4786_,
                    v___y_4787_,
                    v___y_4788_,
                    v___y_4789_,
                );
                if lean_obj_tag(v___x_4801_) == 0 {
                    v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
                    lean_inc_n(v_a_4802_, 2);
                    lean_dec_ref_known(v___x_4801_, 1);
                    lean_inc(v___y_4789_);
                    lean_inc_ref(v___y_4788_);
                    lean_inc(v___y_4787_);
                    lean_inc_ref(v___y_4786_);
                    v___x_4803_ = lean_infer_type(
                        v_a_4802_,
                        v___y_4786_,
                        v___y_4787_,
                        v___y_4788_,
                        v___y_4789_,
                    );
                    if lean_obj_tag(v___x_4803_) == 0 {
                        v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
                        lean_inc(v_a_4804_);
                        lean_dec_ref_known(v___x_4803_, 1);
                        v___x_4805_ = l_Lean_Expr_sortLevel_x21(v_a_4804_);
                        lean_dec(v_a_4804_);
                        lean_inc(v_head_4792_);
                        v___x_4829_ = l_Lean_Expr_occurs(v_head_4792_, v_x_4784_);
                        if v___x_4829_ == 0 {
                            v___x_4830_ = lean_box(0);
                            v___x_4831_ = lean_level_eq(v___x_4805_, v___x_4830_);
                            if v___x_4831_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                v___y_4825_ = v___x_4829_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_4825_ = v___x_4829_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4802_);
                        lean_del_object(v___x_4795_);
                        lean_dec(v_head_4792_);
                        lean_dec_ref(v_x_4784_);
                        v___y_4798_ = v___x_4803_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4795_);
                    lean_dec(v_head_4792_);
                    lean_dec_ref(v_x_4784_);
                    v___y_4798_ = v___x_4801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if lean_obj_tag(v___y_4798_) == 0 {
                    v_a_4799_ = lean_ctor_get(v___y_4798_, 0);
                    lean_inc(v_a_4799_);
                    lean_dec_ref_known(v___y_4798_, 1);
                    v_x_4784_ = v_a_4799_;
                    v_x_4785_ = v_tail_4793_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_4793_);
                    return v___y_4798_;
                }
            }
            3 => {
                v___x_4807_ = 1;
                v___x_4808_ = lean_unsigned_to_nat(1);
                v___x_4809_ = lean_mk_empty_array_with_capacity(v___x_4808_);
                v___x_4810_ = lean_array_push(v___x_4809_, v_head_4792_);
                v___x_4811_ = 0;
                v___x_4812_ = 1;
                v___x_4813_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_4810_,
                    v_x_4784_,
                    v___x_4811_,
                    v___x_4807_,
                    v___x_4811_,
                    v___x_4807_,
                    v___x_4812_,
                    v___y_4786_,
                    v___y_4787_,
                    v___y_4788_,
                    v___y_4789_,
                );
                lean_dec_ref(v___x_4810_);
                if lean_obj_tag(v___x_4813_) == 0 {
                    v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
                    lean_inc(v_a_4814_);
                    lean_dec_ref_known(v___x_4813_, 1);
                    v___x_4815_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__1;
                    v___x_4816_ = lean_box(0);
                    if v_isShared_4796_ == 0 {
                        lean_ctor_set(v___x_4795_, 1, v___x_4816_);
                        lean_ctor_set(v___x_4795_, 0, v___x_4805_);
                        v___x_4818_ = v___x_4795_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4805_);
                        lean_ctor_set(v_reuseFailAlloc_4823_, 1, v___x_4816_);
                        v___x_4818_ = v_reuseFailAlloc_4823_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4805_);
                    lean_dec(v_a_4802_);
                    lean_del_object(v___x_4795_);
                    v___y_4798_ = v___x_4813_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_4819_ = l_Lean_Expr_const___override(v___x_4815_, v___x_4818_);
                v___x_4820_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_updateLambdaBinderInfoD_x21(v_a_4814_);
                v___x_4821_ = l_Lean_mkAppB(v___x_4819_, v_a_4802_, v___x_4820_);
                v_x_4784_ = v___x_4821_;
                v_x_4785_ = v_tail_4793_;
                state = 0;
                continue;
            }
            5 => {
                if v___y_4825_ == 0 {
                    lean_dec(v___x_4805_);
                    lean_del_object(v___x_4795_);
                    lean_dec(v_head_4792_);
                    v___x_4826_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4), core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once), _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
                    v___x_4827_ = l_Lean_mkAppB(v___x_4826_, v_a_4802_, v_x_4784_);
                    v_x_4784_ = v___x_4827_;
                    v_x_4785_ = v_tail_4793_;
                    state = 0;
                    continue;
                } else {
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___boxed(
    mut v_x_4833_: *mut LeanObject,
    mut v_x_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4840_: *mut LeanObject = core::ptr::null_mut();
    v_res_4840_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_x_4833_, v_x_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
    lean_dec(v___y_4838_);
    lean_dec_ref(v___y_4837_);
    lean_dec(v___y_4836_);
    lean_dec_ref(v___y_4835_);
    return v_res_4840_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(
    mut v_args_4841_: *mut LeanObject,
    mut v_inner_4842_: *mut LeanObject,
    mut v_a_4843_: *mut LeanObject,
    mut v_a_4844_: *mut LeanObject,
    mut v_a_4845_: *mut LeanObject,
    mut v_a_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    v___x_4848_ = l_List_reverse___redArg(v_args_4841_);
    v___x_4849_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0(v_inner_4842_, v___x_4848_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
    return v___x_4849_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList___boxed(
    mut v_args_4850_: *mut LeanObject,
    mut v_inner_4851_: *mut LeanObject,
    mut v_a_4852_: *mut LeanObject,
    mut v_a_4853_: *mut LeanObject,
    mut v_a_4854_: *mut LeanObject,
    mut v_a_4855_: *mut LeanObject,
    mut v_a_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4857_: *mut LeanObject = core::ptr::null_mut();
    v_res_4857_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(
        v_args_4850_,
        v_inner_4851_,
        v_a_4852_,
        v_a_4853_,
        v_a_4854_,
        v_a_4855_,
    );
    lean_dec(v_a_4855_);
    lean_dec_ref(v_a_4854_);
    lean_dec(v_a_4853_);
    lean_dec_ref(v_a_4852_);
    return v_res_4857_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(
    mut v_op_4858_: *mut LeanObject,
    mut v_empty_4859_: *mut LeanObject,
    mut v_x_4860_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4860_) == 0 {
        lean_dec_ref(v_op_4858_);
        lean_inc_ref(v_empty_4859_);
        return v_empty_4859_;
    } else {
        let mut v_tail_4861_: *mut LeanObject = core::ptr::null_mut();
        v_tail_4861_ = lean_ctor_get(v_x_4860_, 1);
        if lean_obj_tag(v_tail_4861_) == 0 {
            let mut v_head_4862_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_op_4858_);
            v_head_4862_ = lean_ctor_get(v_x_4860_, 0);
            lean_inc(v_head_4862_);
            lean_dec_ref_known(v_x_4860_, 2);
            return v_head_4862_;
        } else {
            let mut v_head_4863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_4861_);
            v_head_4863_ = lean_ctor_get(v_x_4860_, 0);
            lean_inc(v_head_4863_);
            lean_dec_ref_known(v_x_4860_, 2);
            lean_inc_ref(v_op_4858_);
            v___x_4864_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(
                v_op_4858_,
                v_empty_4859_,
                v_tail_4861_,
            );
            v___x_4865_ = l_Lean_mkAppB(v_op_4858_, v_head_4863_, v___x_4864_);
            return v___x_4865_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList___boxed(
    mut v_op_4866_: *mut LeanObject,
    mut v_empty_4867_: *mut LeanObject,
    mut v_x_4868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4869_: *mut LeanObject = core::ptr::null_mut();
    v_res_4869_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(
        v_op_4866_,
        v_empty_4867_,
        v_x_4868_,
    );
    lean_dec_ref(v_empty_4867_);
    return v_res_4869_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2()
-> *mut LeanObject {
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    v___x_4873_ = lean_box(0);
    v___x_4874_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1;
    v___x_4875_ = l_Lean_mkConst(v___x_4874_, v___x_4873_);
    return v___x_4875_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(
    mut v_a_4876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    v___x_4877_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4), core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4_once), _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList_spec__0___closed__4);
    v___x_4878_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2_once
        ),
        _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__2,
    );
    v___x_4879_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(
        v___x_4877_,
        v___x_4878_,
        v_a_4876_,
    );
    return v___x_4879_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2()
-> *mut LeanObject {
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    v___x_4883_ = lean_box(0);
    v___x_4884_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__1;
    v___x_4885_ = l_Lean_mkConst(v___x_4884_, v___x_4883_);
    return v___x_4885_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5()
-> *mut LeanObject {
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4889_ = lean_box(0);
    v___x_4890_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__4;
    v___x_4891_ = l_Lean_mkConst(v___x_4890_, v___x_4889_);
    return v___x_4891_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(
    mut v_a_4892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    v___x_4893_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2_once
        ),
        _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__2,
    );
    v___x_4894_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5_once
        ),
        _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList___closed__5,
    );
    v___x_4895_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOpList(
        v___x_4893_,
        v___x_4894_,
        v_a_4892_,
    );
    return v___x_4895_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(
    mut v_x_4896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tail_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4901_: u8 = 0;
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4906_: u8 = 0;
    let mut v_unused_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4896_) == 0 {
                    return v_x_4896_;
                } else {
                    v_tail_4897_ = lean_ctor_get(v_x_4896_, 1);
                    lean_inc(v_tail_4897_);
                    if lean_obj_tag(v_tail_4897_) == 0 {
                        lean_dec_ref_known(v_x_4896_, 2);
                        return v_tail_4897_;
                    } else {
                        v_head_4898_ = lean_ctor_get(v_x_4896_, 0);
                        v_isSharedCheck_4906_ = (!lean_is_exclusive(v_x_4896_)) as u8;
                        if v_isSharedCheck_4906_ == 0 {
                            v_unused_4907_ = lean_ctor_get(v_x_4896_, 1);
                            lean_dec(v_unused_4907_);
                            v___x_4900_ = v_x_4896_;
                            v_isShared_4901_ = v_isSharedCheck_4906_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_head_4898_);
                            lean_dec(v_x_4896_);
                            v___x_4900_ = lean_box(0);
                            v_isShared_4901_ = v_isSharedCheck_4906_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4902_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(
                        v_tail_4897_,
                    );
                if v_isShared_4901_ == 0 {
                    lean_ctor_set(v___x_4900_, 1, v___x_4902_);
                    v___x_4904_ = v___x_4900_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_head_4898_);
                    lean_ctor_set(v_reuseFailAlloc_4905_, 1, v___x_4902_);
                    v___x_4904_ = v_reuseFailAlloc_4905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init(
    mut v_00_u03b1_4908_: *mut LeanObject,
    mut v_x_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    v___x_4910_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v_x_4909_);
    return v___x_4910_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(
    mut v_k_4911_: *mut LeanObject,
    mut v_b_4912_: *mut LeanObject,
    mut v_c_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4917_);
    lean_inc_ref(v___y_4916_);
    lean_inc(v___y_4915_);
    lean_inc_ref(v___y_4914_);
    v___x_4919_ = lean_apply_7(
        v_k_4911_,
        v_b_4912_,
        v_c_4913_,
        v___y_4914_,
        v___y_4915_,
        v___y_4916_,
        v___y_4917_,
        lean_box(0),
    );
    return v___x_4919_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed(
    mut v_k_4920_: *mut LeanObject,
    mut v_b_4921_: *mut LeanObject,
    mut v_c_4922_: *mut LeanObject,
    mut v___y_4923_: *mut LeanObject,
    mut v___y_4924_: *mut LeanObject,
    mut v___y_4925_: *mut LeanObject,
    mut v___y_4926_: *mut LeanObject,
    mut v___y_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4928_: *mut LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0(v_k_4920_, v_b_4921_, v_c_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
    lean_dec(v___y_4926_);
    lean_dec_ref(v___y_4925_);
    lean_dec(v___y_4924_);
    lean_dec_ref(v___y_4923_);
    return v_res_4928_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(
    mut v_type_4929_: *mut LeanObject,
    mut v_maxFVars_x3f_4930_: *mut LeanObject,
    mut v_k_4931_: *mut LeanObject,
    mut v_cleanupAnnotations_4932_: u8,
    mut v_whnfType_4933_: u8,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4948_: u8 = 0;
    let mut v_a_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4939_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_4939_, 0, v_k_4931_);
                v___x_4940_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_4929_,
                    v_maxFVars_x3f_4930_,
                    v___f_4939_,
                    v_cleanupAnnotations_4932_,
                    v_whnfType_4933_,
                    v___y_4934_,
                    v___y_4935_,
                    v___y_4936_,
                    v___y_4937_,
                );
                if lean_obj_tag(v___x_4940_) == 0 {
                    v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_4948_ = (!lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_4948_ == 0 {
                        v___x_4943_ = v___x_4940_;
                        v_isShared_4944_ = v_isSharedCheck_4948_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4941_);
                        lean_dec(v___x_4940_);
                        v___x_4943_ = lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4948_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4949_ = lean_ctor_get(v___x_4940_, 0);
                    v_isSharedCheck_4956_ = (!lean_is_exclusive(v___x_4940_)) as u8;
                    if v_isSharedCheck_4956_ == 0 {
                        v___x_4951_ = v___x_4940_;
                        v_isShared_4952_ = v_isSharedCheck_4956_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4949_);
                        lean_dec(v___x_4940_);
                        v___x_4951_ = lean_box(0);
                        v_isShared_4952_ = v_isSharedCheck_4956_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4944_ == 0 {
                    v___x_4946_ = v___x_4943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
                    v___x_4946_ = v_reuseFailAlloc_4947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4946_;
            }
            3 => {
                if v_isShared_4952_ == 0 {
                    v___x_4954_ = v___x_4951_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___boxed(
    mut v_type_4957_: *mut LeanObject,
    mut v_maxFVars_x3f_4958_: *mut LeanObject,
    mut v_k_4959_: *mut LeanObject,
    mut v_cleanupAnnotations_4960_: *mut LeanObject,
    mut v_whnfType_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4967_: u8 = 0;
    let mut v_whnfType_boxed_4968_: u8 = 0;
    let mut v_res_4969_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4967_ = (lean_unbox(v_cleanupAnnotations_4960_) as u8);
    v_whnfType_boxed_4968_ = (lean_unbox(v_whnfType_4961_) as u8);
    v_res_4969_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_4957_, v_maxFVars_x3f_4958_, v_k_4959_, v_cleanupAnnotations_boxed_4967_, v_whnfType_boxed_4968_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
    lean_dec(v___y_4965_);
    lean_dec_ref(v___y_4964_);
    lean_dec(v___y_4963_);
    lean_dec_ref(v___y_4962_);
    return v_res_4969_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(
    mut v_00_u03b1_4970_: *mut LeanObject,
    mut v_type_4971_: *mut LeanObject,
    mut v_maxFVars_x3f_4972_: *mut LeanObject,
    mut v_k_4973_: *mut LeanObject,
    mut v_cleanupAnnotations_4974_: u8,
    mut v_whnfType_4975_: u8,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    v___x_4981_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v_type_4971_, v_maxFVars_x3f_4972_, v_k_4973_, v_cleanupAnnotations_4974_, v_whnfType_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
    return v___x_4981_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___boxed(
    mut v_00_u03b1_4982_: *mut LeanObject,
    mut v_type_4983_: *mut LeanObject,
    mut v_maxFVars_x3f_4984_: *mut LeanObject,
    mut v_k_4985_: *mut LeanObject,
    mut v_cleanupAnnotations_4986_: *mut LeanObject,
    mut v_whnfType_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_4993_: u8 = 0;
    let mut v_whnfType_boxed_4994_: u8 = 0;
    let mut v_res_4995_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4993_ = (lean_unbox(v_cleanupAnnotations_4986_) as u8);
    v_whnfType_boxed_4994_ = (lean_unbox(v_whnfType_4987_) as u8);
    v_res_4995_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4(v_00_u03b1_4982_, v_type_4983_, v_maxFVars_x3f_4984_, v_k_4985_, v_cleanupAnnotations_boxed_4993_, v_whnfType_boxed_4994_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
    lean_dec(v___y_4991_);
    lean_dec_ref(v___y_4990_);
    lean_dec(v___y_4989_);
    lean_dec_ref(v___y_4988_);
    return v_res_4995_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(
    mut v_type_4996_: *mut LeanObject,
    mut v_k_4997_: *mut LeanObject,
    mut v_cleanupAnnotations_4998_: u8,
    mut v___y_4999_: *mut LeanObject,
    mut v___y_5000_: *mut LeanObject,
    mut v___y_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: u8 = 0;
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_a_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5004_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_5004_, 0, v_k_4997_);
                v___x_5005_ = 0;
                v___x_5006_ = lean_box(0);
                v___x_5007_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        lean_box(0),
                        v___x_5005_,
                        v___x_5006_,
                        v_type_4996_,
                        v___f_5004_,
                        v_cleanupAnnotations_4998_,
                        v___x_5005_,
                        v___y_4999_,
                        v___y_5000_,
                        v___y_5001_,
                        v___y_5002_,
                    );
                if lean_obj_tag(v___x_5007_) == 0 {
                    v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
                    v_isSharedCheck_5015_ = (!lean_is_exclusive(v___x_5007_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5010_ = v___x_5007_;
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5008_);
                        lean_dec(v___x_5007_);
                        v___x_5010_ = lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5016_ = lean_ctor_get(v___x_5007_, 0);
                    v_isSharedCheck_5023_ = (!lean_is_exclusive(v___x_5007_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v___x_5018_ = v___x_5007_;
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5016_);
                        lean_dec(v___x_5007_);
                        v___x_5018_ = lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5011_ == 0 {
                    v___x_5013_ = v___x_5010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5013_;
            }
            3 => {
                if v_isShared_5019_ == 0 {
                    v___x_5021_ = v___x_5018_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg___boxed(
    mut v_type_5024_: *mut LeanObject,
    mut v_k_5025_: *mut LeanObject,
    mut v_cleanupAnnotations_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5032_: u8 = 0;
    let mut v_res_5033_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5032_ = (lean_unbox(v_cleanupAnnotations_5026_) as u8);
    v_res_5033_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_5024_, v_k_5025_, v_cleanupAnnotations_boxed_5032_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
    lean_dec(v___y_5030_);
    lean_dec_ref(v___y_5029_);
    lean_dec(v___y_5028_);
    lean_dec_ref(v___y_5027_);
    return v_res_5033_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(
    mut v_00_u03b1_5034_: *mut LeanObject,
    mut v_type_5035_: *mut LeanObject,
    mut v_k_5036_: *mut LeanObject,
    mut v_cleanupAnnotations_5037_: u8,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    v___x_5043_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_type_5035_, v_k_5036_, v_cleanupAnnotations_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
    return v___x_5043_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___boxed(
    mut v_00_u03b1_5044_: *mut LeanObject,
    mut v_type_5045_: *mut LeanObject,
    mut v_k_5046_: *mut LeanObject,
    mut v_cleanupAnnotations_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5053_: u8 = 0;
    let mut v_res_5054_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5053_ = (lean_unbox(v_cleanupAnnotations_5047_) as u8);
    v_res_5054_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5(v_00_u03b1_5044_, v_type_5045_, v_k_5046_, v_cleanupAnnotations_boxed_5053_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
    lean_dec(v___y_5051_);
    lean_dec_ref(v___y_5050_);
    lean_dec(v___y_5049_);
    lean_dec_ref(v___y_5048_);
    return v_res_5054_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(
    mut v_params_5055_: *mut LeanObject,
    mut v_fvars_5056_: *mut LeanObject,
    mut v_ty_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5063_ = lean_array_mk(v_params_5055_);
    v___x_5064_ = l_Lean_Expr_replaceFVars(v_ty_5057_, v_fvars_5056_, v___x_5063_);
    lean_dec_ref(v___x_5063_);
    v___x_5065_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5065_, 0, v___x_5064_);
    return v___x_5065_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed(
    mut v_params_5066_: *mut LeanObject,
    mut v_fvars_5067_: *mut LeanObject,
    mut v_ty_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5074_: *mut LeanObject = core::ptr::null_mut();
    v_res_5074_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0(
        v_params_5066_,
        v_fvars_5067_,
        v_ty_5068_,
        v___y_5069_,
        v___y_5070_,
        v___y_5071_,
        v___y_5072_,
    );
    lean_dec(v___y_5072_);
    lean_dec_ref(v___y_5071_);
    lean_dec(v___y_5070_);
    lean_dec_ref(v___y_5069_);
    lean_dec_ref(v_ty_5068_);
    lean_dec_ref(v_fvars_5067_);
    return v_res_5074_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(
    mut v_x_5081_: *mut LeanObject,
    mut v_x_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v_a_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5107_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5111_: u8 = 0;
    let mut v_fst_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5116_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5145_: u8 = 0;
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5081_) == 0 {
                    v___x_5088_ = l_List_reverse___redArg(v_x_5082_);
                    v___x_5089_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5089_, 0, v___x_5088_);
                    return v___x_5089_;
                } else {
                    v_head_5090_ = lean_ctor_get(v_x_5081_, 0);
                    v_tail_5091_ = lean_ctor_get(v_x_5081_, 1);
                    v_isSharedCheck_5151_ = (!lean_is_exclusive(v_x_5081_)) as u8;
                    if v_isSharedCheck_5151_ == 0 {
                        v___x_5093_ = v_x_5081_;
                        v_isShared_5094_ = v_isSharedCheck_5151_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5091_);
                        lean_inc(v_head_5090_);
                        lean_dec(v_x_5081_);
                        v___x_5093_ = lean_box(0);
                        v_isShared_5094_ = v_isSharedCheck_5151_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5112_ = lean_ctor_get(v_head_5090_, 0);
                v_snd_5113_ = lean_ctor_get(v_head_5090_, 1);
                v_isSharedCheck_5150_ = (!lean_is_exclusive(v_head_5090_)) as u8;
                if v_isSharedCheck_5150_ == 0 {
                    v___x_5115_ = v_head_5090_;
                    v_isShared_5116_ = v_isSharedCheck_5150_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_5113_);
                    lean_inc(v_fst_5112_);
                    lean_dec(v_head_5090_);
                    v___x_5115_ = lean_box(0);
                    v_isShared_5116_ = v_isSharedCheck_5150_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                if v_isShared_5094_ == 0 {
                    lean_ctor_set(v___x_5093_, 1, v_x_5082_);
                    lean_ctor_set(v___x_5093_, 0, v_a_5096_);
                    v___x_5098_ = v___x_5093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5100_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5100_, 0, v_a_5096_);
                    lean_ctor_set(v_reuseFailAlloc_5100_, 1, v_x_5082_);
                    v___x_5098_ = v_reuseFailAlloc_5100_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_5081_ = v_tail_5091_;
                v_x_5082_ = v___x_5098_;
                state = 0;
                continue;
            }
            4 => {
                if lean_obj_tag(v___y_5102_) == 0 {
                    v_a_5103_ = lean_ctor_get(v___y_5102_, 0);
                    lean_inc(v_a_5103_);
                    lean_dec_ref_known(v___y_5102_, 1);
                    v_a_5096_ = v_a_5103_;
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_5093_);
                    lean_dec(v_tail_5091_);
                    lean_dec(v_x_5082_);
                    v_a_5104_ = lean_ctor_get(v___y_5102_, 0);
                    v_isSharedCheck_5111_ = (!lean_is_exclusive(v___y_5102_)) as u8;
                    if v_isSharedCheck_5111_ == 0 {
                        v___x_5106_ = v___y_5102_;
                        v_isShared_5107_ = v_isSharedCheck_5111_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5104_);
                        lean_dec(v___y_5102_);
                        v___x_5106_ = lean_box(0);
                        v_isShared_5107_ = v_isSharedCheck_5111_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5107_ == 0 {
                    v___x_5109_ = v___x_5106_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
                    v___x_5109_ = v_reuseFailAlloc_5110_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5109_;
            }
            7 => {
                v___x_5117_ = l_Lean_Expr_fvarId_x21(v_fst_5112_);
                v___x_5118_ = l_Lean_FVarId_getType___redArg(
                    v___x_5117_,
                    v___y_5083_,
                    v___y_5085_,
                    v___y_5086_,
                );
                if lean_obj_tag(v___x_5118_) == 0 {
                    v_a_5119_ = lean_ctor_get(v___x_5118_, 0);
                    lean_inc(v_a_5119_);
                    lean_dec_ref_known(v___x_5118_, 1);
                    lean_inc(v___y_5086_);
                    lean_inc_ref(v___y_5085_);
                    lean_inc(v___y_5084_);
                    lean_inc_ref(v___y_5083_);
                    lean_inc(v_snd_5113_);
                    v___x_5120_ = lean_infer_type(
                        v_snd_5113_,
                        v___y_5083_,
                        v___y_5084_,
                        v___y_5085_,
                        v___y_5086_,
                    );
                    if lean_obj_tag(v___x_5120_) == 0 {
                        v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
                        lean_inc(v_a_5121_);
                        lean_dec_ref_known(v___x_5120_, 1);
                        lean_inc(v___y_5086_);
                        lean_inc_ref(v___y_5085_);
                        lean_inc(v___y_5084_);
                        lean_inc_ref(v___y_5083_);
                        lean_inc(v_a_5119_);
                        v___x_5122_ = lean_infer_type(
                            v_a_5119_,
                            v___y_5083_,
                            v___y_5084_,
                            v___y_5085_,
                            v___y_5086_,
                        );
                        if lean_obj_tag(v___x_5122_) == 0 {
                            v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
                            lean_inc(v_a_5123_);
                            lean_dec_ref_known(v___x_5122_, 1);
                            lean_inc(v_a_5121_);
                            lean_inc(v_a_5119_);
                            v___x_5124_ = l_Lean_Meta_isExprDefEq(
                                v_a_5119_,
                                v_a_5121_,
                                v___y_5083_,
                                v___y_5084_,
                                v___y_5085_,
                                v___y_5086_,
                            );
                            if lean_obj_tag(v___x_5124_) == 0 {
                                v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
                                lean_inc(v_a_5125_);
                                lean_dec_ref_known(v___x_5124_, 1);
                                v___x_5126_ = l_Lean_Expr_sortLevel_x21(v_a_5123_);
                                lean_dec(v_a_5123_);
                                v___x_5127_ = (lean_unbox(v_a_5125_) as u8);
                                lean_dec(v_a_5125_);
                                if v___x_5127_ == 0 {
                                    v___x_5128_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__1;
                                    v___x_5129_ = lean_box(0);
                                    if v_isShared_5116_ == 0 {
                                        lean_ctor_set_tag(v___x_5115_, 1);
                                        lean_ctor_set(v___x_5115_, 1, v___x_5129_);
                                        lean_ctor_set(v___x_5115_, 0, v___x_5126_);
                                        v___x_5131_ = v___x_5115_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5126_);
                                        lean_ctor_set(v_reuseFailAlloc_5134_, 1, v___x_5129_);
                                        v___x_5131_ = v_reuseFailAlloc_5134_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_5121_);
                                    v___x_5135_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___closed__3;
                                    v___x_5136_ = lean_box(0);
                                    if v_isShared_5116_ == 0 {
                                        lean_ctor_set_tag(v___x_5115_, 1);
                                        lean_ctor_set(v___x_5115_, 1, v___x_5136_);
                                        lean_ctor_set(v___x_5115_, 0, v___x_5126_);
                                        v___x_5138_ = v___x_5115_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5141_, 0, v___x_5126_);
                                        lean_ctor_set(v_reuseFailAlloc_5141_, 1, v___x_5136_);
                                        v___x_5138_ = v_reuseFailAlloc_5141_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5123_);
                                lean_dec(v_a_5121_);
                                lean_dec(v_a_5119_);
                                lean_del_object(v___x_5115_);
                                lean_dec(v_snd_5113_);
                                lean_dec(v_fst_5112_);
                                lean_del_object(v___x_5093_);
                                lean_dec(v_tail_5091_);
                                lean_dec(v_x_5082_);
                                v_a_5142_ = lean_ctor_get(v___x_5124_, 0);
                                v_isSharedCheck_5149_ = (!lean_is_exclusive(v___x_5124_)) as u8;
                                if v_isSharedCheck_5149_ == 0 {
                                    v___x_5144_ = v___x_5124_;
                                    v_isShared_5145_ = v_isSharedCheck_5149_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_5142_);
                                    lean_dec(v___x_5124_);
                                    v___x_5144_ = lean_box(0);
                                    v_isShared_5145_ = v_isSharedCheck_5149_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5121_);
                            lean_dec(v_a_5119_);
                            lean_del_object(v___x_5115_);
                            lean_dec(v_snd_5113_);
                            lean_dec(v_fst_5112_);
                            v___y_5102_ = v___x_5122_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5119_);
                        lean_del_object(v___x_5115_);
                        lean_dec(v_snd_5113_);
                        lean_dec(v_fst_5112_);
                        v___y_5102_ = v___x_5120_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5115_);
                    lean_dec(v_snd_5113_);
                    lean_dec(v_fst_5112_);
                    v___y_5102_ = v___x_5118_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_5132_ = l_Lean_Expr_const___override(v___x_5128_, v___x_5131_);
                v___x_5133_ =
                    l_Lean_mkApp4(v___x_5132_, v_a_5119_, v_fst_5112_, v_a_5121_, v_snd_5113_);
                v_a_5096_ = v___x_5133_;
                state = 2;
                continue;
            }
            9 => {
                v___x_5139_ = l_Lean_Expr_const___override(v___x_5135_, v___x_5138_);
                v___x_5140_ = l_Lean_mkApp3(v___x_5139_, v_a_5119_, v_fst_5112_, v_snd_5113_);
                v_a_5096_ = v___x_5140_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_5145_ == 0 {
                    v___x_5147_ = v___x_5144_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5148_, 0, v_a_5142_);
                    v___x_5147_ = v_reuseFailAlloc_5148_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2___boxed(
    mut v_x_5152_: *mut LeanObject,
    mut v_x_5153_: *mut LeanObject,
    mut v___y_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5159_: *mut LeanObject = core::ptr::null_mut();
    v_res_5159_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_x_5152_, v_x_5153_, v___y_5154_, v___y_5155_, v___y_5156_, v___y_5157_);
    lean_dec(v___y_5157_);
    lean_dec_ref(v___y_5156_);
    lean_dec(v___y_5155_);
    lean_dec_ref(v___y_5154_);
    return v_res_5159_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(
    mut v_a_5160_: *mut LeanObject,
    mut v_a_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5160_) == 0 {
                    v___x_5162_ = lean_array_to_list(v_a_5161_);
                    return v___x_5162_;
                } else {
                    v_head_5163_ = lean_ctor_get(v_a_5160_, 0);
                    if lean_obj_tag(v_head_5163_) == 0 {
                        v_tail_5164_ = lean_ctor_get(v_a_5160_, 1);
                        lean_inc(v_tail_5164_);
                        lean_dec_ref_known(v_a_5160_, 2);
                        v_a_5160_ = v_tail_5164_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc_ref(v_head_5163_);
                        v_tail_5166_ = lean_ctor_get(v_a_5160_, 1);
                        lean_inc(v_tail_5166_);
                        lean_dec_ref_known(v_a_5160_, 2);
                        v_val_5167_ = lean_ctor_get(v_head_5163_, 0);
                        lean_inc(v_val_5167_);
                        lean_dec_ref_known(v_head_5163_, 1);
                        v___x_5168_ = lean_array_push(v_a_5161_, v_val_5167_);
                        v_a_5160_ = v_tail_5166_;
                        v_a_5161_ = v___x_5168_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(
    mut v_a_5170_: *mut LeanObject,
    mut v_a_5171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5177_: u8 = 0;
    let mut v___y_5179_: u8 = 0;
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: u8 = 0;
    let mut v___x_5186_: u8 = 0;
    let mut v_isSharedCheck_5187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5170_) == 0 {
                    v___x_5172_ = l_List_reverse___redArg(v_a_5171_);
                    return v___x_5172_;
                } else {
                    v_head_5173_ = lean_ctor_get(v_a_5170_, 0);
                    v_tail_5174_ = lean_ctor_get(v_a_5170_, 1);
                    v_isSharedCheck_5187_ = (!lean_is_exclusive(v_a_5170_)) as u8;
                    if v_isSharedCheck_5187_ == 0 {
                        v___x_5176_ = v_a_5170_;
                        v_isShared_5177_ = v_isSharedCheck_5187_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5174_);
                        lean_inc(v_head_5173_);
                        lean_dec(v_a_5170_);
                        v___x_5176_ = lean_box(0);
                        v_isShared_5177_ = v_isSharedCheck_5187_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_head_5173_) == 0 {
                    v___x_5185_ = 0;
                    v___y_5179_ = v___x_5185_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref_known(v_head_5173_, 1);
                    v___x_5186_ = 1;
                    v___y_5179_ = v___x_5186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5180_ = lean_box((v___y_5179_) as usize);
                if v_isShared_5177_ == 0 {
                    lean_ctor_set(v___x_5176_, 1, v_a_5171_);
                    lean_ctor_set(v___x_5176_, 0, v___x_5180_);
                    v___x_5182_ = v___x_5176_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5180_);
                    lean_ctor_set(v_reuseFailAlloc_5184_, 1, v_a_5171_);
                    v___x_5182_ = v_reuseFailAlloc_5184_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_5170_ = v_tail_5174_;
                v_a_5171_ = v___x_5182_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0()
-> *mut LeanObject {
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5189_: *mut LeanObject = core::ptr::null_mut();
    v___x_5188_ = lean_box(0);
    v_dummy_5189_ = l_Lean_Expr_sort___override(v___x_5188_);
    return v_dummy_5189_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    v___x_5194_ = lean_box(0);
    v___x_5195_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList___closed__1;
    v___x_5196_ = l_Lean_mkConst(v___x_5195_, v___x_5194_);
    return v___x_5196_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(
    mut v___x_5197_: *mut LeanObject,
    mut v_idxs_5198_: *mut LeanObject,
    mut v___x_5199_: *mut LeanObject,
    mut v_fvars_5200_: *mut LeanObject,
    mut v_ty_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5223_: u8 = 0;
    let mut v_fst_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5254_: u8 = 0;
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5258_: u8 = 0;
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: u8 = 0;
    let mut v___x_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5296_: u8 = 0;
    let mut v_a_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5300_: u8 = 0;
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5304_: u8 = 0;
    let mut v_a_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v_a_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5316_: u8 = 0;
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5320_: u8 = 0;
    let mut v_isSharedCheck_5321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5207_ = lean_box(0);
                v_dummy_5208_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__0);
                v_nargs_5209_ = l_Lean_Expr_getAppNumArgs(v_ty_5201_);
                lean_inc(v_nargs_5209_);
                v___x_5210_ = lean_mk_array(v_nargs_5209_, v_dummy_5208_);
                v___x_5211_ = lean_unsigned_to_nat(1);
                v___x_5212_ = lean_nat_sub(v_nargs_5209_, v___x_5211_);
                lean_dec(v_nargs_5209_);
                v___x_5213_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_ty_5201_,
                    v___x_5210_,
                    v___x_5212_,
                );
                v___x_5214_ = lean_array_to_list(v___x_5213_);
                v___x_5215_ = l_List_drop___redArg(v___x_5197_, v___x_5214_);
                lean_dec(v___x_5214_);
                v___x_5216_ = lean_array_to_list(v_fvars_5200_);
                v___x_5217_ = l_List_zipWith___at___00List_zip_spec__0(
                    lean_box(0),
                    lean_box(0),
                    v_idxs_5198_,
                    v___x_5215_,
                );
                v___x_5218_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_compactRelation(
                        v___x_5216_,
                        v___x_5217_,
                    );
                v_fst_5219_ = lean_ctor_get(v___x_5218_, 0);
                v_snd_5220_ = lean_ctor_get(v___x_5218_, 1);
                v_isSharedCheck_5321_ = (!lean_is_exclusive(v___x_5218_)) as u8;
                if v_isSharedCheck_5321_ == 0 {
                    v___x_5222_ = v___x_5218_;
                    v_isShared_5223_ = v_isSharedCheck_5321_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_5220_);
                    lean_inc(v_fst_5219_);
                    lean_dec(v___x_5218_);
                    v___x_5222_ = lean_box(0);
                    v_isShared_5223_ = v_isSharedCheck_5321_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_5234_ = lean_ctor_get(v_snd_5220_, 0);
                lean_inc(v_fst_5234_);
                v_snd_5235_ = lean_ctor_get(v_snd_5220_, 1);
                lean_inc(v_snd_5235_);
                lean_dec(v_snd_5220_);
                v___x_5236_ = lean_box(0);
                v___x_5237_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__2(v_fst_5234_, v___x_5236_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
                if lean_obj_tag(v___x_5237_) == 0 {
                    v_a_5238_ = lean_ctor_get(v___x_5237_, 0);
                    lean_inc(v_a_5238_);
                    lean_dec_ref_known(v___x_5237_, 1);
                    v___x_5259_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1;
                    lean_inc(v_fst_5219_);
                    v___x_5260_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__3(v_fst_5219_, v___x_5259_);
                    if lean_obj_tag(v___x_5260_) == 0 {
                        if lean_obj_tag(v_a_5238_) == 0 {
                            lean_dec(v_snd_5235_);
                            v___x_5261_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2;
                            v___x_5262_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
                            v_fst_5225_ = v___x_5261_;
                            v_snd_5226_ = v___x_5262_;
                            state = 2;
                            continue;
                        } else {
                            v_bs_x27_5240_ = v___x_5260_;
                            v___y_5241_ = v___y_5202_;
                            v___y_5242_ = v___y_5203_;
                            v___y_5243_ = v___y_5204_;
                            v___y_5244_ = v___y_5205_;
                            state = 4;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_a_5238_) == 0 {
                            v___x_5263_ = l_List_getLast_x21___redArg(v___x_5199_, v___x_5260_);
                            v___x_5264_ = l_Lean_Expr_fvarId_x21(v___x_5263_);
                            lean_dec(v___x_5263_);
                            v___x_5265_ = l_Lean_FVarId_getType___redArg(
                                v___x_5264_,
                                v___y_5202_,
                                v___y_5204_,
                                v___y_5205_,
                            );
                            if lean_obj_tag(v___x_5265_) == 0 {
                                v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
                                lean_inc_n(v_a_5266_, 2);
                                lean_dec_ref_known(v___x_5265_, 1);
                                lean_inc(v___y_5205_);
                                lean_inc_ref(v___y_5204_);
                                lean_inc(v___y_5203_);
                                lean_inc_ref(v___y_5202_);
                                v___x_5267_ = lean_infer_type(
                                    v_a_5266_,
                                    v___y_5202_,
                                    v___y_5203_,
                                    v___y_5204_,
                                    v___y_5205_,
                                );
                                if lean_obj_tag(v___x_5267_) == 0 {
                                    v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
                                    lean_inc(v_a_5268_);
                                    lean_dec_ref_known(v___x_5267_, 1);
                                    v___x_5269_ = l_Lean_Expr_sortLevel_x21(v_a_5268_);
                                    lean_dec(v_a_5268_);
                                    v___x_5270_ = lean_level_eq(v___x_5269_, v___x_5207_);
                                    lean_dec(v___x_5269_);
                                    if v___x_5270_ == 0 {
                                        lean_dec(v_a_5266_);
                                        v___x_5271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__3);
                                        v___x_5272_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_5260_, v___x_5271_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
                                        if lean_obj_tag(v___x_5272_) == 0 {
                                            v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
                                            lean_inc(v_a_5273_);
                                            lean_dec_ref_known(v___x_5272_, 1);
                                            v___x_5274_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__2;
                                            v___x_5275_ = lean_apply_1(v_snd_5235_, v_a_5273_);
                                            v_fst_5225_ = v___x_5274_;
                                            v_snd_5226_ = v___x_5275_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec(v_snd_5235_);
                                            lean_del_object(v___x_5222_);
                                            lean_dec(v_fst_5219_);
                                            v_a_5276_ = lean_ctor_get(v___x_5272_, 0);
                                            v_isSharedCheck_5283_ =
                                                (!lean_is_exclusive(v___x_5272_)) as u8;
                                            if v_isSharedCheck_5283_ == 0 {
                                                v___x_5278_ = v___x_5272_;
                                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5276_);
                                                lean_dec(v___x_5272_);
                                                v___x_5278_ = lean_box(0);
                                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                                state = 7;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v___x_5284_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_5260_);
                                        v___x_5285_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(v___x_5284_, v_a_5266_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
                                        if lean_obj_tag(v___x_5285_) == 0 {
                                            v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
                                            lean_inc(v_a_5286_);
                                            lean_dec_ref_known(v___x_5285_, 1);
                                            v___x_5287_ = lean_box(0);
                                            v___x_5288_ = lean_apply_1(v_snd_5235_, v_a_5286_);
                                            v_fst_5225_ = v___x_5287_;
                                            v_snd_5226_ = v___x_5288_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec(v_snd_5235_);
                                            lean_del_object(v___x_5222_);
                                            lean_dec(v_fst_5219_);
                                            v_a_5289_ = lean_ctor_get(v___x_5285_, 0);
                                            v_isSharedCheck_5296_ =
                                                (!lean_is_exclusive(v___x_5285_)) as u8;
                                            if v_isSharedCheck_5296_ == 0 {
                                                v___x_5291_ = v___x_5285_;
                                                v_isShared_5292_ = v_isSharedCheck_5296_;
                                                state = 9;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5289_);
                                                lean_dec(v___x_5285_);
                                                v___x_5291_ = lean_box(0);
                                                v_isShared_5292_ = v_isSharedCheck_5296_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5266_);
                                    lean_dec(v___x_5260_);
                                    lean_dec(v_snd_5235_);
                                    lean_del_object(v___x_5222_);
                                    lean_dec(v_fst_5219_);
                                    v_a_5297_ = lean_ctor_get(v___x_5267_, 0);
                                    v_isSharedCheck_5304_ = (!lean_is_exclusive(v___x_5267_)) as u8;
                                    if v_isSharedCheck_5304_ == 0 {
                                        v___x_5299_ = v___x_5267_;
                                        v_isShared_5300_ = v_isSharedCheck_5304_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5297_);
                                        lean_dec(v___x_5267_);
                                        v___x_5299_ = lean_box(0);
                                        v_isShared_5300_ = v_isSharedCheck_5304_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_5260_);
                                lean_dec(v_snd_5235_);
                                lean_del_object(v___x_5222_);
                                lean_dec(v_fst_5219_);
                                v_a_5305_ = lean_ctor_get(v___x_5265_, 0);
                                v_isSharedCheck_5312_ = (!lean_is_exclusive(v___x_5265_)) as u8;
                                if v_isSharedCheck_5312_ == 0 {
                                    v___x_5307_ = v___x_5265_;
                                    v_isShared_5308_ = v_isSharedCheck_5312_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_5305_);
                                    lean_dec(v___x_5265_);
                                    v___x_5307_ = lean_box(0);
                                    v_isShared_5308_ = v_isSharedCheck_5312_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            v_bs_x27_5240_ = v___x_5260_;
                            v___y_5241_ = v___y_5202_;
                            v___y_5242_ = v___y_5203_;
                            v___y_5243_ = v___y_5204_;
                            v___y_5244_ = v___y_5205_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_5235_);
                    lean_del_object(v___x_5222_);
                    lean_dec(v_fst_5219_);
                    v_a_5313_ = lean_ctor_get(v___x_5237_, 0);
                    v_isSharedCheck_5320_ = (!lean_is_exclusive(v___x_5237_)) as u8;
                    if v_isSharedCheck_5320_ == 0 {
                        v___x_5315_ = v___x_5237_;
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5313_);
                        lean_dec(v___x_5237_);
                        v___x_5315_ = lean_box(0);
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5227_ = lean_box(0);
                v___x_5228_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__1(v_fst_5219_, v___x_5227_);
                v___x_5229_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5229_, 0, v___x_5228_);
                lean_ctor_set(v___x_5229_, 1, v_fst_5225_);
                if v_isShared_5223_ == 0 {
                    lean_ctor_set(v___x_5222_, 1, v_snd_5226_);
                    lean_ctor_set(v___x_5222_, 0, v___x_5229_);
                    v___x_5231_ = v___x_5222_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5229_);
                    lean_ctor_set(v_reuseFailAlloc_5233_, 1, v_snd_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5233_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5232_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5232_, 0, v___x_5231_);
                return v___x_5232_;
            }
            4 => {
                lean_inc(v_a_5238_);
                v___x_5245_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkAndList(v_a_5238_);
                v___x_5246_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkExistsList(
                    v_bs_x27_5240_,
                    v___x_5245_,
                    v___y_5241_,
                    v___y_5242_,
                    v___y_5243_,
                    v___y_5244_,
                );
                if lean_obj_tag(v___x_5246_) == 0 {
                    v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
                    lean_inc(v_a_5247_);
                    lean_dec_ref_known(v___x_5246_, 1);
                    v___x_5248_ = l_List_lengthTR___redArg(v_a_5238_);
                    lean_dec(v_a_5238_);
                    v___x_5249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5249_, 0, v___x_5248_);
                    v___x_5250_ = lean_apply_1(v_snd_5235_, v_a_5247_);
                    v_fst_5225_ = v___x_5249_;
                    v_snd_5226_ = v___x_5250_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_a_5238_);
                    lean_dec(v_snd_5235_);
                    lean_del_object(v___x_5222_);
                    lean_dec(v_fst_5219_);
                    v_a_5251_ = lean_ctor_get(v___x_5246_, 0);
                    v_isSharedCheck_5258_ = (!lean_is_exclusive(v___x_5246_)) as u8;
                    if v_isSharedCheck_5258_ == 0 {
                        v___x_5253_ = v___x_5246_;
                        v_isShared_5254_ = v_isSharedCheck_5258_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5251_);
                        lean_dec(v___x_5246_);
                        v___x_5253_ = lean_box(0);
                        v_isShared_5254_ = v_isSharedCheck_5258_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5254_ == 0 {
                    v___x_5256_ = v___x_5253_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5257_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5257_, 0, v_a_5251_);
                    v___x_5256_ = v_reuseFailAlloc_5257_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5256_;
            }
            7 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5281_;
            }
            9 => {
                if v_isShared_5292_ == 0 {
                    v___x_5294_ = v___x_5291_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
                    v___x_5294_ = v_reuseFailAlloc_5295_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5294_;
            }
            11 => {
                if v_isShared_5300_ == 0 {
                    v___x_5302_ = v___x_5299_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
                    v___x_5302_ = v_reuseFailAlloc_5303_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5302_;
            }
            13 => {
                if v_isShared_5308_ == 0 {
                    v___x_5310_ = v___x_5307_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
                    v___x_5310_ = v_reuseFailAlloc_5311_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5310_;
            }
            15 => {
                if v_isShared_5316_ == 0 {
                    v___x_5318_ = v___x_5315_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
                    v___x_5318_ = v_reuseFailAlloc_5319_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed(
    mut v___x_5322_: *mut LeanObject,
    mut v_idxs_5323_: *mut LeanObject,
    mut v___x_5324_: *mut LeanObject,
    mut v_fvars_5325_: *mut LeanObject,
    mut v_ty_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
    mut v___y_5331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5332_: *mut LeanObject = core::ptr::null_mut();
    v_res_5332_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1(
        v___x_5322_,
        v_idxs_5323_,
        v___x_5324_,
        v_fvars_5325_,
        v_ty_5326_,
        v___y_5327_,
        v___y_5328_,
        v___y_5329_,
        v___y_5330_,
    );
    lean_dec(v___y_5330_);
    lean_dec_ref(v___y_5329_);
    lean_dec(v___y_5328_);
    lean_dec_ref(v___y_5327_);
    lean_dec_ref(v___x_5324_);
    return v_res_5332_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(
    mut v_ref_5333_: *mut LeanObject,
    mut v_msg_5334_: *mut LeanObject,
    mut v___y_5335_: *mut LeanObject,
    mut v___y_5336_: *mut LeanObject,
    mut v___y_5337_: *mut LeanObject,
    mut v___y_5338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5352_: u8 = 0;
    let mut v_cancelTk_x3f_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5354_: u8 = 0;
    let mut v_inheritedTraceOptions_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5340_ = lean_ctor_get(v___y_5337_, 0);
    v_fileMap_5341_ = lean_ctor_get(v___y_5337_, 1);
    v_options_5342_ = lean_ctor_get(v___y_5337_, 2);
    v_currRecDepth_5343_ = lean_ctor_get(v___y_5337_, 3);
    v_maxRecDepth_5344_ = lean_ctor_get(v___y_5337_, 4);
    v_ref_5345_ = lean_ctor_get(v___y_5337_, 5);
    v_currNamespace_5346_ = lean_ctor_get(v___y_5337_, 6);
    v_openDecls_5347_ = lean_ctor_get(v___y_5337_, 7);
    v_initHeartbeats_5348_ = lean_ctor_get(v___y_5337_, 8);
    v_maxHeartbeats_5349_ = lean_ctor_get(v___y_5337_, 9);
    v_quotContext_5350_ = lean_ctor_get(v___y_5337_, 10);
    v_currMacroScope_5351_ = lean_ctor_get(v___y_5337_, 11);
    v_diag_5352_ = lean_ctor_get_uint8(
        v___y_5337_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5353_ = lean_ctor_get(v___y_5337_, 12);
    v_suppressElabErrors_5354_ = lean_ctor_get_uint8(
        v___y_5337_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5355_ = lean_ctor_get(v___y_5337_, 13);
    v_ref_5356_ = l_Lean_replaceRef(v_ref_5333_, v_ref_5345_);
    lean_inc_ref(v_inheritedTraceOptions_5355_);
    lean_inc(v_cancelTk_x3f_5353_);
    lean_inc(v_currMacroScope_5351_);
    lean_inc(v_quotContext_5350_);
    lean_inc(v_maxHeartbeats_5349_);
    lean_inc(v_initHeartbeats_5348_);
    lean_inc(v_openDecls_5347_);
    lean_inc(v_currNamespace_5346_);
    lean_inc(v_maxRecDepth_5344_);
    lean_inc(v_currRecDepth_5343_);
    lean_inc_ref(v_options_5342_);
    lean_inc_ref(v_fileMap_5341_);
    lean_inc_ref(v_fileName_5340_);
    v___x_5357_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5357_, 0, v_fileName_5340_);
    lean_ctor_set(v___x_5357_, 1, v_fileMap_5341_);
    lean_ctor_set(v___x_5357_, 2, v_options_5342_);
    lean_ctor_set(v___x_5357_, 3, v_currRecDepth_5343_);
    lean_ctor_set(v___x_5357_, 4, v_maxRecDepth_5344_);
    lean_ctor_set(v___x_5357_, 5, v_ref_5356_);
    lean_ctor_set(v___x_5357_, 6, v_currNamespace_5346_);
    lean_ctor_set(v___x_5357_, 7, v_openDecls_5347_);
    lean_ctor_set(v___x_5357_, 8, v_initHeartbeats_5348_);
    lean_ctor_set(v___x_5357_, 9, v_maxHeartbeats_5349_);
    lean_ctor_set(v___x_5357_, 10, v_quotContext_5350_);
    lean_ctor_set(v___x_5357_, 11, v_currMacroScope_5351_);
    lean_ctor_set(v___x_5357_, 12, v_cancelTk_x3f_5353_);
    lean_ctor_set(v___x_5357_, 13, v_inheritedTraceOptions_5355_);
    lean_ctor_set_uint8(
        v___x_5357_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5352_,
    );
    lean_ctor_set_uint8(
        v___x_5357_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5354_,
    );
    v___x_5358_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v_msg_5334_, v___y_5335_, v___y_5336_, v___x_5357_, v___y_5338_);
    lean_dec_ref_known(v___x_5357_, 14);
    return v___x_5358_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg___boxed(
    mut v_ref_5359_: *mut LeanObject,
    mut v_msg_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5366_: *mut LeanObject = core::ptr::null_mut();
    v_res_5366_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_5359_, v_msg_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
    lean_dec(v___y_5364_);
    lean_dec_ref(v___y_5363_);
    lean_dec(v___y_5362_);
    lean_dec_ref(v___y_5361_);
    lean_dec(v_ref_5359_);
    return v_res_5366_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    v___x_5367_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5367_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut LeanObject = core::ptr::null_mut();
    v___x_5368_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_5369_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5369_, 0, v___x_5368_);
    return v___x_5369_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    v___x_5370_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5371_ = lean_unsigned_to_nat(0);
    v___x_5372_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_5372_, 0, v___x_5371_);
    lean_ctor_set(v___x_5372_, 1, v___x_5371_);
    lean_ctor_set(v___x_5372_, 2, v___x_5371_);
    lean_ctor_set(v___x_5372_, 3, v___x_5371_);
    lean_ctor_set(v___x_5372_, 4, v___x_5370_);
    lean_ctor_set(v___x_5372_, 5, v___x_5370_);
    lean_ctor_set(v___x_5372_, 6, v___x_5370_);
    lean_ctor_set(v___x_5372_, 7, v___x_5370_);
    lean_ctor_set(v___x_5372_, 8, v___x_5370_);
    lean_ctor_set(v___x_5372_, 9, v___x_5370_);
    return v___x_5372_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    v___x_5373_ = lean_unsigned_to_nat(32);
    v___x_5374_ = lean_mk_empty_array_with_capacity(v___x_5373_);
    v___x_5375_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5375_, 0, v___x_5374_);
    return v___x_5375_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    v___x_5376_ = 5usize;
    v___x_5377_ = lean_unsigned_to_nat(0);
    v___x_5378_ = lean_unsigned_to_nat(32);
    v___x_5379_ = lean_mk_empty_array_with_capacity(v___x_5378_);
    v___x_5380_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_5381_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5381_, 0, v___x_5380_);
    lean_ctor_set(v___x_5381_, 1, v___x_5379_);
    lean_ctor_set(v___x_5381_, 2, v___x_5377_);
    lean_ctor_set(v___x_5381_, 3, v___x_5377_);
    lean_ctor_set_usize(v___x_5381_, 4, v___x_5376_);
    return v___x_5381_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    v___x_5382_ = lean_box(1);
    v___x_5383_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_5384_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_5385_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_5385_, 0, v___x_5384_);
    lean_ctor_set(v___x_5385_, 1, v___x_5383_);
    lean_ctor_set(v___x_5385_, 2, v___x_5382_);
    return v___x_5385_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    v___x_5387_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_5388_ = l_Lean_stringToMessageData(v___x_5387_);
    return v___x_5388_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    v___x_5390_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_5391_ = l_Lean_stringToMessageData(v___x_5390_);
    return v___x_5391_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    v___x_5393_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_5394_ = l_Lean_stringToMessageData(v___x_5393_);
    return v___x_5394_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    v___x_5396_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_5397_ = l_Lean_stringToMessageData(v___x_5396_);
    return v___x_5397_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_5400_ = l_Lean_stringToMessageData(v___x_5399_);
    return v___x_5400_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    v___x_5402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_5403_ = l_Lean_stringToMessageData(v___x_5402_);
    return v___x_5403_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    v___x_5405_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_5406_ = l_Lean_stringToMessageData(v___x_5405_);
    return v___x_5406_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(
    mut v_msg_5407_: *mut LeanObject,
    mut v_declHint_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: u8 = 0;
    let mut v_isExporting_5414_: u8 = 0;
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: u8 = 0;
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5411_ = lean_st_ref_get(v___y_5409_);
                v_env_5412_ = lean_ctor_get(v___x_5411_, 0);
                lean_inc_ref(v_env_5412_);
                lean_dec(v___x_5411_);
                v___x_5413_ = l_Lean_Name_isAnonymous(v_declHint_5408_);
                if v___x_5413_ == 0 {
                    v_isExporting_5414_ = lean_ctor_get_uint8(
                        v_env_5412_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_5414_ == 0 {
                        lean_dec_ref(v_env_5412_);
                        lean_dec(v_declHint_5408_);
                        v___x_5415_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5415_, 0, v_msg_5407_);
                        return v___x_5415_;
                    } else {
                        lean_inc_ref(v_env_5412_);
                        v___x_5416_ = l_Lean_Environment_setExporting(v_env_5412_, v___x_5413_);
                        lean_inc(v_declHint_5408_);
                        lean_inc_ref(v___x_5416_);
                        v___x_5417_ = l_Lean_Environment_contains(
                            v___x_5416_,
                            v_declHint_5408_,
                            v_isExporting_5414_,
                        );
                        if v___x_5417_ == 0 {
                            lean_dec_ref(v___x_5416_);
                            lean_dec_ref(v_env_5412_);
                            lean_dec(v_declHint_5408_);
                            v___x_5418_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_5418_, 0, v_msg_5407_);
                            return v___x_5418_;
                        } else {
                            v___x_5419_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_5420_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_5421_ = l_Lean_Options_empty;
                            v___x_5422_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_5422_, 0, v___x_5416_);
                            lean_ctor_set(v___x_5422_, 1, v___x_5419_);
                            lean_ctor_set(v___x_5422_, 2, v___x_5420_);
                            lean_ctor_set(v___x_5422_, 3, v___x_5421_);
                            lean_inc(v_declHint_5408_);
                            v___x_5423_ =
                                l_Lean_MessageData_ofConstName(v_declHint_5408_, v___x_5413_);
                            v_c_5424_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_5424_, 0, v___x_5422_);
                            lean_ctor_set(v_c_5424_, 1, v___x_5423_);
                            v___x_5425_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_5412_,
                                v_declHint_5408_,
                            );
                            if lean_obj_tag(v___x_5425_) == 0 {
                                lean_dec_ref(v_env_5412_);
                                lean_dec(v_declHint_5408_);
                                v___x_5426_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_5427_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5427_, 0, v___x_5426_);
                                lean_ctor_set(v___x_5427_, 1, v_c_5424_);
                                v___x_5428_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_5429_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5429_, 0, v___x_5427_);
                                lean_ctor_set(v___x_5429_, 1, v___x_5428_);
                                v___x_5430_ = l_Lean_MessageData_note(v___x_5429_);
                                v___x_5431_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_5431_, 0, v_msg_5407_);
                                lean_ctor_set(v___x_5431_, 1, v___x_5430_);
                                v___x_5432_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_5432_, 0, v___x_5431_);
                                return v___x_5432_;
                            } else {
                                v_val_5433_ = lean_ctor_get(v___x_5425_, 0);
                                v_isSharedCheck_5468_ = (!lean_is_exclusive(v___x_5425_)) as u8;
                                if v_isSharedCheck_5468_ == 0 {
                                    v___x_5435_ = v___x_5425_;
                                    v_isShared_5436_ = v_isSharedCheck_5468_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_5433_);
                                    lean_dec(v___x_5425_);
                                    v___x_5435_ = lean_box(0);
                                    v_isShared_5436_ = v_isSharedCheck_5468_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_5412_);
                    lean_dec(v_declHint_5408_);
                    v___x_5469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5469_, 0, v_msg_5407_);
                    return v___x_5469_;
                }
            }
            1 => {
                v___x_5437_ = lean_box(0);
                v___x_5438_ = l_Lean_Environment_header(v_env_5412_);
                lean_dec_ref(v_env_5412_);
                v___x_5439_ = l_Lean_EnvironmentHeader_moduleNames(v___x_5438_);
                v_mod_5440_ = lean_array_get(v___x_5437_, v___x_5439_, v_val_5433_);
                lean_dec(v_val_5433_);
                lean_dec_ref(v___x_5439_);
                v___x_5441_ = l_Lean_isPrivateName(v_declHint_5408_);
                lean_dec(v_declHint_5408_);
                if v___x_5441_ == 0 {
                    v___x_5442_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_5443_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5443_, 0, v___x_5442_);
                    lean_ctor_set(v___x_5443_, 1, v_c_5424_);
                    v___x_5444_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_5445_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5445_, 0, v___x_5443_);
                    lean_ctor_set(v___x_5445_, 1, v___x_5444_);
                    v___x_5446_ = l_Lean_MessageData_ofName(v_mod_5440_);
                    v___x_5447_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5447_, 0, v___x_5445_);
                    lean_ctor_set(v___x_5447_, 1, v___x_5446_);
                    v___x_5448_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_5449_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5449_, 0, v___x_5447_);
                    lean_ctor_set(v___x_5449_, 1, v___x_5448_);
                    v___x_5450_ = l_Lean_MessageData_note(v___x_5449_);
                    v___x_5451_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5451_, 0, v_msg_5407_);
                    lean_ctor_set(v___x_5451_, 1, v___x_5450_);
                    if v_isShared_5436_ == 0 {
                        lean_ctor_set_tag(v___x_5435_, 0);
                        lean_ctor_set(v___x_5435_, 0, v___x_5451_);
                        v___x_5453_ = v___x_5435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5454_, 0, v___x_5451_);
                        v___x_5453_ = v_reuseFailAlloc_5454_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5455_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_5456_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5456_, 0, v___x_5455_);
                    lean_ctor_set(v___x_5456_, 1, v_c_5424_);
                    v___x_5457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_5458_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5458_, 0, v___x_5456_);
                    lean_ctor_set(v___x_5458_, 1, v___x_5457_);
                    v___x_5459_ = l_Lean_MessageData_ofName(v_mod_5440_);
                    v___x_5460_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5460_, 0, v___x_5458_);
                    lean_ctor_set(v___x_5460_, 1, v___x_5459_);
                    v___x_5461_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_5462_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5462_, 0, v___x_5460_);
                    lean_ctor_set(v___x_5462_, 1, v___x_5461_);
                    v___x_5463_ = l_Lean_MessageData_note(v___x_5462_);
                    v___x_5464_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5464_, 0, v_msg_5407_);
                    lean_ctor_set(v___x_5464_, 1, v___x_5463_);
                    if v_isShared_5436_ == 0 {
                        lean_ctor_set_tag(v___x_5435_, 0);
                        lean_ctor_set(v___x_5435_, 0, v___x_5464_);
                        v___x_5466_ = v___x_5435_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
                        v___x_5466_ = v_reuseFailAlloc_5467_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5453_;
            }
            3 => {
                return v___x_5466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_5470_: *mut LeanObject,
    mut v_declHint_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5474_: *mut LeanObject = core::ptr::null_mut();
    v_res_5474_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_5470_, v_declHint_5471_, v___y_5472_);
    lean_dec(v___y_5472_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(
    mut v_msg_5475_: *mut LeanObject,
    mut v_declHint_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5486_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_5475_, v_declHint_5476_, v___y_5480_);
                v_a_5483_ = lean_ctor_get(v___x_5482_, 0);
                v_isSharedCheck_5492_ = (!lean_is_exclusive(v___x_5482_)) as u8;
                if v_isSharedCheck_5492_ == 0 {
                    v___x_5485_ = v___x_5482_;
                    v_isShared_5486_ = v_isSharedCheck_5492_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5483_);
                    lean_dec(v___x_5482_);
                    v___x_5485_ = lean_box(0);
                    v_isShared_5486_ = v_isSharedCheck_5492_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5487_ = l_Lean_unknownIdentifierMessageTag;
                v___x_5488_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_5488_, 0, v___x_5487_);
                lean_ctor_set(v___x_5488_, 1, v_a_5483_);
                if v_isShared_5486_ == 0 {
                    lean_ctor_set(v___x_5485_, 0, v___x_5488_);
                    v___x_5490_ = v___x_5485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8___boxed(
    mut v_msg_5493_: *mut LeanObject,
    mut v_declHint_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
    mut v___y_5498_: *mut LeanObject,
    mut v___y_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5500_: *mut LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_5493_, v_declHint_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_);
    lean_dec(v___y_5498_);
    lean_dec_ref(v___y_5497_);
    lean_dec(v___y_5496_);
    lean_dec_ref(v___y_5495_);
    return v_res_5500_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(
    mut v_ref_5501_: *mut LeanObject,
    mut v_msg_5502_: *mut LeanObject,
    mut v_declHint_5503_: *mut LeanObject,
    mut v___y_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
    v___x_5509_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8(v_msg_5502_, v_declHint_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
    lean_inc(v_a_5510_);
    lean_dec_ref(v___x_5509_);
    v___x_5511_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_5501_, v_a_5510_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    return v___x_5511_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg___boxed(
    mut v_ref_5512_: *mut LeanObject,
    mut v_msg_5513_: *mut LeanObject,
    mut v_declHint_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5520_: *mut LeanObject = core::ptr::null_mut();
    v_res_5520_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5512_, v_msg_5513_, v_declHint_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
    lean_dec(v___y_5518_);
    lean_dec_ref(v___y_5517_);
    lean_dec(v___y_5516_);
    lean_dec_ref(v___y_5515_);
    lean_dec(v_ref_5512_);
    return v_res_5520_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    v___x_5522_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_5523_ = l_Lean_stringToMessageData(v___x_5522_);
    return v___x_5523_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    v___x_5525_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_5526_ = l_Lean_stringToMessageData(v___x_5525_);
    return v___x_5526_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(
    mut v_ref_5527_: *mut LeanObject,
    mut v_constName_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: u8 = 0;
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    v___x_5534_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_5535_ = 0;
    lean_inc(v_constName_5528_);
    v___x_5536_ = l_Lean_MessageData_ofConstName(v_constName_5528_, v___x_5535_);
    v___x_5537_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5537_, 0, v___x_5534_);
    lean_ctor_set(v___x_5537_, 1, v___x_5536_);
    v___x_5538_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_5539_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5539_, 0, v___x_5537_);
    lean_ctor_set(v___x_5539_, 1, v___x_5538_);
    v___x_5540_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5527_, v___x_5539_, v_constName_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
    return v___x_5540_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_5541_: *mut LeanObject,
    mut v_constName_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5548_: *mut LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_5541_, v_constName_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
    lean_dec(v___y_5546_);
    lean_dec_ref(v___y_5545_);
    lean_dec(v___y_5544_);
    lean_dec_ref(v___y_5543_);
    lean_dec(v_ref_5541_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(
    mut v_constName_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
    mut v___y_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5555_ = lean_ctor_get(v___y_5552_, 5);
    v___x_5556_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_5555_, v_constName_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
    return v___x_5556_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg___boxed(
    mut v_constName_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5563_: *mut LeanObject = core::ptr::null_mut();
    v_res_5563_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_);
    lean_dec(v___y_5561_);
    lean_dec_ref(v___y_5560_);
    lean_dec(v___y_5559_);
    lean_dec_ref(v___y_5558_);
    return v_res_5563_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(
    mut v_constName_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
    mut v___y_5566_: *mut LeanObject,
    mut v___y_5567_: *mut LeanObject,
    mut v___y_5568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: u8 = 0;
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5570_ = lean_st_ref_get(v___y_5568_);
                v_env_5571_ = lean_ctor_get(v___x_5570_, 0);
                lean_inc_ref(v_env_5571_);
                lean_dec(v___x_5570_);
                v___x_5572_ = 0;
                lean_inc(v_constName_5564_);
                v___x_5573_ =
                    l_Lean_Environment_find_x3f(v_env_5571_, v_constName_5564_, v___x_5572_);
                if lean_obj_tag(v___x_5573_) == 0 {
                    v___x_5574_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_5564_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
                    return v___x_5574_;
                } else {
                    lean_dec(v_constName_5564_);
                    v_val_5575_ = lean_ctor_get(v___x_5573_, 0);
                    v_isSharedCheck_5582_ = (!lean_is_exclusive(v___x_5573_)) as u8;
                    if v_isSharedCheck_5582_ == 0 {
                        v___x_5577_ = v___x_5573_;
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5575_);
                        lean_dec(v___x_5573_);
                        v___x_5577_ = lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5578_ == 0 {
                    lean_ctor_set_tag(v___x_5577_, 0);
                    v___x_5580_ = v___x_5577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_val_5575_);
                    v___x_5580_ = v_reuseFailAlloc_5581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0___boxed(
    mut v_constName_5583_: *mut LeanObject,
    mut v___y_5584_: *mut LeanObject,
    mut v___y_5585_: *mut LeanObject,
    mut v___y_5586_: *mut LeanObject,
    mut v___y_5587_: *mut LeanObject,
    mut v___y_5588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5589_: *mut LeanObject = core::ptr::null_mut();
    v_res_5589_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_constName_5583_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
    lean_dec(v___y_5587_);
    lean_dec_ref(v___y_5586_);
    lean_dec(v___y_5585_);
    lean_dec_ref(v___y_5584_);
    return v_res_5589_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(
    mut v_univs_5590_: *mut LeanObject,
    mut v_params_5591_: *mut LeanObject,
    mut v_idxs_5592_: *mut LeanObject,
    mut v_c_5593_: *mut LeanObject,
    mut v_a_5594_: *mut LeanObject,
    mut v_a_5595_: *mut LeanObject,
    mut v_a_5596_: *mut LeanObject,
    mut v_a_5597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: u8 = 0;
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut v_a_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5622_: u8 = 0;
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5599_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_c_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_);
                if lean_obj_tag(v___x_5599_) == 0 {
                    v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
                    lean_inc(v_a_5600_);
                    lean_dec_ref_known(v___x_5599_, 1);
                    lean_inc(v_params_5591_);
                    v___f_5601_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    lean_closure_set(v___f_5601_, 0, v_params_5591_);
                    v___x_5602_ =
                        l_Lean_ConstantInfo_instantiateTypeLevelParams(v_a_5600_, v_univs_5590_);
                    lean_dec(v_a_5600_);
                    v___x_5603_ = l_List_lengthTR___redArg(v_params_5591_);
                    lean_dec(v_params_5591_);
                    lean_inc(v___x_5603_);
                    v___x_5604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5604_, 0, v___x_5603_);
                    v___x_5605_ = 0;
                    v___x_5606_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg(v___x_5602_, v___x_5604_, v___f_5601_, v___x_5605_, v___x_5605_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_);
                    if lean_obj_tag(v___x_5606_) == 0 {
                        v_a_5607_ = lean_ctor_get(v___x_5606_, 0);
                        lean_inc(v_a_5607_);
                        lean_dec_ref_known(v___x_5606_, 1);
                        v___x_5608_ = l_Lean_instInhabitedExpr;
                        v___f_5609_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                        lean_closure_set(v___f_5609_, 0, v___x_5603_);
                        lean_closure_set(v___f_5609_, 1, v_idxs_5592_);
                        lean_closure_set(v___f_5609_, 2, v___x_5608_);
                        v___x_5610_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__5___redArg(v_a_5607_, v___f_5609_, v___x_5605_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_);
                        return v___x_5610_;
                    } else {
                        lean_dec(v___x_5603_);
                        lean_dec(v_idxs_5592_);
                        v_a_5611_ = lean_ctor_get(v___x_5606_, 0);
                        v_isSharedCheck_5618_ = (!lean_is_exclusive(v___x_5606_)) as u8;
                        if v_isSharedCheck_5618_ == 0 {
                            v___x_5613_ = v___x_5606_;
                            v_isShared_5614_ = v_isSharedCheck_5618_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5611_);
                            lean_dec(v___x_5606_);
                            v___x_5613_ = lean_box(0);
                            v_isShared_5614_ = v_isSharedCheck_5618_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_idxs_5592_);
                    lean_dec(v_params_5591_);
                    lean_dec(v_univs_5590_);
                    v_a_5619_ = lean_ctor_get(v___x_5599_, 0);
                    v_isSharedCheck_5626_ = (!lean_is_exclusive(v___x_5599_)) as u8;
                    if v_isSharedCheck_5626_ == 0 {
                        v___x_5621_ = v___x_5599_;
                        v_isShared_5622_ = v_isSharedCheck_5626_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5619_);
                        lean_dec(v___x_5599_);
                        v___x_5621_ = lean_box(0);
                        v_isShared_5622_ = v_isSharedCheck_5626_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5614_ == 0 {
                    v___x_5616_ = v___x_5613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
                    v___x_5616_ = v_reuseFailAlloc_5617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5616_;
            }
            3 => {
                if v_isShared_5622_ == 0 {
                    v___x_5624_ = v___x_5621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5619_);
                    v___x_5624_ = v_reuseFailAlloc_5625_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___boxed(
    mut v_univs_5627_: *mut LeanObject,
    mut v_params_5628_: *mut LeanObject,
    mut v_idxs_5629_: *mut LeanObject,
    mut v_c_5630_: *mut LeanObject,
    mut v_a_5631_: *mut LeanObject,
    mut v_a_5632_: *mut LeanObject,
    mut v_a_5633_: *mut LeanObject,
    mut v_a_5634_: *mut LeanObject,
    mut v_a_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5636_: *mut LeanObject = core::ptr::null_mut();
    v_res_5636_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(
        v_univs_5627_,
        v_params_5628_,
        v_idxs_5629_,
        v_c_5630_,
        v_a_5631_,
        v_a_5632_,
        v_a_5633_,
        v_a_5634_,
    );
    lean_dec(v_a_5634_);
    lean_dec_ref(v_a_5633_);
    lean_dec(v_a_5632_);
    lean_dec_ref(v_a_5631_);
    return v_res_5636_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(
    mut v_00_u03b1_5637_: *mut LeanObject,
    mut v_constName_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    v___x_5644_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
    return v___x_5644_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___boxed(
    mut v_00_u03b1_5645_: *mut LeanObject,
    mut v_constName_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
    mut v___y_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5652_: *mut LeanObject = core::ptr::null_mut();
    v_res_5652_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0(v_00_u03b1_5645_, v_constName_5646_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_);
    lean_dec(v___y_5650_);
    lean_dec_ref(v___y_5649_);
    lean_dec(v___y_5648_);
    lean_dec_ref(v___y_5647_);
    return v_res_5652_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(
    mut v_00_u03b1_5653_: *mut LeanObject,
    mut v_ref_5654_: *mut LeanObject,
    mut v_constName_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    v___x_5661_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___redArg(v_ref_5654_, v_constName_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
    return v___x_5661_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_5662_: *mut LeanObject,
    mut v_ref_5663_: *mut LeanObject,
    mut v_constName_5664_: *mut LeanObject,
    mut v___y_5665_: *mut LeanObject,
    mut v___y_5666_: *mut LeanObject,
    mut v___y_5667_: *mut LeanObject,
    mut v___y_5668_: *mut LeanObject,
    mut v___y_5669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5670_: *mut LeanObject = core::ptr::null_mut();
    v_res_5670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3(v_00_u03b1_5662_, v_ref_5663_, v_constName_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
    lean_dec(v___y_5668_);
    lean_dec_ref(v___y_5667_);
    lean_dec(v___y_5666_);
    lean_dec_ref(v___y_5665_);
    lean_dec(v_ref_5663_);
    return v_res_5670_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(
    mut v_00_u03b1_5671_: *mut LeanObject,
    mut v_ref_5672_: *mut LeanObject,
    mut v_msg_5673_: *mut LeanObject,
    mut v_declHint_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
    mut v___y_5678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    v___x_5680_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___redArg(v_ref_5672_, v_msg_5673_, v_declHint_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_);
    return v___x_5680_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7___boxed(
    mut v_00_u03b1_5681_: *mut LeanObject,
    mut v_ref_5682_: *mut LeanObject,
    mut v_msg_5683_: *mut LeanObject,
    mut v_declHint_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5690_: *mut LeanObject = core::ptr::null_mut();
    v_res_5690_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7(v_00_u03b1_5681_, v_ref_5682_, v_msg_5683_, v_declHint_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_);
    lean_dec(v___y_5688_);
    lean_dec_ref(v___y_5687_);
    lean_dec(v___y_5686_);
    lean_dec_ref(v___y_5685_);
    lean_dec(v_ref_5682_);
    return v_res_5690_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(
    mut v_msg_5691_: *mut LeanObject,
    mut v_declHint_5692_: *mut LeanObject,
    mut v___y_5693_: *mut LeanObject,
    mut v___y_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    v___x_5698_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___redArg(v_msg_5691_, v_declHint_5692_, v___y_5696_);
    return v___x_5698_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9___boxed(
    mut v_msg_5699_: *mut LeanObject,
    mut v_declHint_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5706_: *mut LeanObject = core::ptr::null_mut();
    v_res_5706_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__8_spec__9(v_msg_5699_, v_declHint_5700_, v___y_5701_, v___y_5702_, v___y_5703_, v___y_5704_);
    lean_dec(v___y_5704_);
    lean_dec_ref(v___y_5703_);
    lean_dec(v___y_5702_);
    lean_dec_ref(v___y_5701_);
    return v_res_5706_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(
    mut v_00_u03b1_5707_: *mut LeanObject,
    mut v_ref_5708_: *mut LeanObject,
    mut v_msg_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    v___x_5715_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_ref_5708_, v_msg_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
    return v___x_5715_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9___boxed(
    mut v_00_u03b1_5716_: *mut LeanObject,
    mut v_ref_5717_: *mut LeanObject,
    mut v_msg_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5724_: *mut LeanObject = core::ptr::null_mut();
    v_res_5724_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0_spec__3_spec__7_spec__9(v_00_u03b1_5716_, v_ref_5717_, v_msg_5718_, v___y_5719_, v___y_5720_, v___y_5721_, v___y_5722_);
    lean_dec(v___y_5722_);
    lean_dec_ref(v___y_5721_);
    lean_dec(v___y_5720_);
    lean_dec_ref(v___y_5719_);
    lean_dec(v_ref_5717_);
    return v_res_5724_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
    mut v___y_5734_: *mut LeanObject,
    mut v___y_5735_: *mut LeanObject,
    mut v___y_5736_: *mut LeanObject,
    mut v___y_5737_: *mut LeanObject,
    mut v___y_5738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5740_ = lean_ctor_get(v___y_5737_, 5);
    v___x_5741_ = 0;
    v___x_5742_ = l_Lean_SourceInfo_fromRef(v_ref_5740_, v___x_5741_);
    v___x_5743_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0;
    v___x_5744_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1;
    lean_inc(v___x_5742_);
    v___x_5745_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5745_, 0, v___x_5742_);
    lean_ctor_set(v___x_5745_, 1, v___x_5743_);
    v___x_5746_ = l_Lean_Syntax_node1(v___x_5742_, v___x_5744_, v___x_5745_);
    v___x_5747_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_5746_,
        v___y_5731_,
        v___y_5732_,
        v___y_5733_,
        v___y_5734_,
        v___y_5735_,
        v___y_5736_,
        v___y_5737_,
        v___y_5738_,
    );
    return v___x_5747_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___boxed(
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5757_: *mut LeanObject = core::ptr::null_mut();
    v_res_5757_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1(
            v___y_5748_,
            v___y_5749_,
            v___y_5750_,
            v___y_5751_,
            v___y_5752_,
            v___y_5753_,
            v___y_5754_,
            v___y_5755_,
        );
    lean_dec(v___y_5755_);
    lean_dec_ref(v___y_5754_);
    lean_dec(v___y_5753_);
    lean_dec_ref(v___y_5752_);
    lean_dec(v___y_5751_);
    lean_dec_ref(v___y_5750_);
    lean_dec(v___y_5749_);
    lean_dec_ref(v___y_5748_);
    return v_res_5757_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(
    mut v_isZero_5758_: u8,
    mut v_x_5759_: *mut LeanObject,
) -> u8 {
    return v_isZero_5758_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed(
    mut v_isZero_5760_: *mut LeanObject,
    mut v_x_5761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_5762_: u8 = 0;
    let mut v_res_5763_: u8 = 0;
    let mut v_r_5764_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5762_ = (lean_unbox(v_isZero_5760_) as u8);
    v_res_5763_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0(
            v_isZero_boxed_5762_,
            v_x_5761_,
        );
    lean_dec(v_x_5761_);
    v_r_5764_ = lean_box((v_res_5763_) as usize);
    return v_r_5764_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(
    mut v_isZero_5765_: u8,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5775_ = lean_ctor_get(v___y_5772_, 5);
    v___x_5776_ = l_Lean_SourceInfo_fromRef(v_ref_5775_, v_isZero_5765_);
    v___x_5777_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__3;
    v___x_5778_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__4;
    lean_inc_n(v___x_5776_, 9);
    v___x_5779_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5779_, 0, v___x_5776_);
    lean_ctor_set(v___x_5779_, 1, v___x_5777_);
    v___x_5780_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__7;
    v___x_5781_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__8;
    v___x_5782_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5782_, 0, v___x_5776_);
    lean_ctor_set(v___x_5782_, 1, v___x_5781_);
    v___x_5783_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__10;
    v___x_5784_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__12;
    v___x_5785_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__13;
    v___x_5786_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5786_, 0, v___x_5776_);
    lean_ctor_set(v___x_5786_, 1, v___x_5785_);
    v___x_5787_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__14;
    v___x_5788_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5788_, 0, v___x_5776_);
    lean_ctor_set(v___x_5788_, 1, v___x_5787_);
    v___x_5789_ = l_Lean_Syntax_node2(v___x_5776_, v___x_5784_, v___x_5786_, v___x_5788_);
    v___x_5790_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__15;
    v___x_5791_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5791_, 0, v___x_5776_);
    lean_ctor_set(v___x_5791_, 1, v___x_5790_);
    lean_inc(v___x_5789_);
    v___x_5792_ = l_Lean_Syntax_node3(
        v___x_5776_,
        v___x_5783_,
        v___x_5789_,
        v___x_5791_,
        v___x_5789_,
    );
    v___x_5793_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___lam__1___closed__16;
    v___x_5794_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5794_, 0, v___x_5776_);
    lean_ctor_set(v___x_5794_, 1, v___x_5793_);
    v___x_5795_ = l_Lean_Syntax_node3(
        v___x_5776_,
        v___x_5780_,
        v___x_5782_,
        v___x_5792_,
        v___x_5794_,
    );
    v___x_5796_ = l_Lean_Syntax_node2(v___x_5776_, v___x_5778_, v___x_5779_, v___x_5795_);
    v___x_5797_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_5796_,
        v___y_5766_,
        v___y_5767_,
        v___y_5768_,
        v___y_5769_,
        v___y_5770_,
        v___y_5771_,
        v___y_5772_,
        v___y_5773_,
    );
    return v___x_5797_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed(
    mut v_isZero_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_5808_: u8 = 0;
    let mut v_res_5809_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5808_ = (lean_unbox(v_isZero_5798_) as u8);
    v_res_5809_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2(
            v_isZero_boxed_5808_,
            v___y_5799_,
            v___y_5800_,
            v___y_5801_,
            v___y_5802_,
            v___y_5803_,
            v___y_5804_,
            v___y_5805_,
            v___y_5806_,
        );
    lean_dec(v___y_5806_);
    lean_dec_ref(v___y_5805_);
    lean_dec(v___y_5804_);
    lean_dec_ref(v___y_5803_);
    lean_dec(v___y_5802_);
    lean_dec_ref(v___y_5801_);
    lean_dec(v___y_5800_);
    lean_dec_ref(v___y_5799_);
    return v_res_5809_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(
    mut v_isZero_5810_: u8,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
    mut v___y_5813_: *mut LeanObject,
    mut v___y_5814_: *mut LeanObject,
    mut v___y_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5820_ = lean_ctor_get(v___y_5817_, 5);
    v___x_5821_ = l_Lean_SourceInfo_fromRef(v_ref_5820_, v_isZero_5810_);
    v___x_5822_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__0;
    v___x_5823_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__1___closed__1;
    lean_inc(v___x_5821_);
    v___x_5824_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_5824_, 0, v___x_5821_);
    lean_ctor_set(v___x_5824_, 1, v___x_5822_);
    v___x_5825_ = l_Lean_Syntax_node1(v___x_5821_, v___x_5823_, v___x_5824_);
    v___x_5826_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_5825_,
        v___y_5811_,
        v___y_5812_,
        v___y_5813_,
        v___y_5814_,
        v___y_5815_,
        v___y_5816_,
        v___y_5817_,
        v___y_5818_,
    );
    return v___x_5826_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed(
    mut v_isZero_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
    mut v___y_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
    mut v___y_5832_: *mut LeanObject,
    mut v___y_5833_: *mut LeanObject,
    mut v___y_5834_: *mut LeanObject,
    mut v___y_5835_: *mut LeanObject,
    mut v___y_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isZero_boxed_5837_: u8 = 0;
    let mut v_res_5838_: *mut LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5837_ = (lean_unbox(v_isZero_5827_) as u8);
    v_res_5838_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3(
            v_isZero_boxed_5837_,
            v___y_5828_,
            v___y_5829_,
            v___y_5830_,
            v___y_5831_,
            v___y_5832_,
            v___y_5833_,
            v___y_5834_,
            v___y_5835_,
        );
    lean_dec(v___y_5835_);
    lean_dec_ref(v___y_5834_);
    lean_dec(v___y_5833_);
    lean_dec_ref(v___y_5832_);
    lean_dec(v___y_5831_);
    lean_dec_ref(v___y_5830_);
    lean_dec(v___y_5829_);
    lean_dec_ref(v___y_5828_);
    return v_res_5838_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2()
-> *mut LeanObject {
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    v___x_5841_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__1;
    v___x_5842_ = l_Lean_stringToMessageData(v___x_5841_);
    return v___x_5842_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(
    mut v_mvar_5843_: *mut LeanObject,
    mut v_n_5844_: *mut LeanObject,
    mut v_a_5845_: *mut LeanObject,
    mut v_a_5846_: *mut LeanObject,
    mut v_a_5847_: *mut LeanObject,
    mut v_a_5848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5858_: u8 = 0;
    let mut v___f_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: u8 = 0;
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5873_: u8 = 0;
    let mut v_fst_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5881_: u8 = 0;
    let mut v_a_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5885_: u8 = 0;
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: u8 = 0;
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5923_: u8 = 0;
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5857_ = lean_unsigned_to_nat(0);
                v_isZero_5858_ = lean_nat_dec_eq(v_n_5844_, v_zero_5857_);
                if v_isZero_5858_ == 1 {
                    lean_dec(v_n_5844_);
                    v___f_5859_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__2;
                    v___f_5860_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__0;
                    v___x_5861_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_5861_, 0, v_mvar_5843_);
                    lean_closure_set(v___x_5861_, 1, v___f_5860_);
                    v___x_5862_ = lean_box(0);
                    v___x_5863_ = lean_box(0);
                    v___x_5864_ = lean_box(1);
                    v___x_5865_ = 0;
                    v___x_5866_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4;
                    v___x_5867_ = lean_alloc_ctor(0, 8, (11) as u32);
                    lean_ctor_set(v___x_5867_, 0, v___x_5862_);
                    lean_ctor_set(v___x_5867_, 1, v___x_5863_);
                    lean_ctor_set(v___x_5867_, 2, v___x_5862_);
                    lean_ctor_set(v___x_5867_, 3, v___f_5859_);
                    lean_ctor_set(v___x_5867_, 4, v___x_5864_);
                    lean_ctor_set(v___x_5867_, 5, v___x_5864_);
                    lean_ctor_set(v___x_5867_, 6, v___x_5862_);
                    lean_ctor_set(v___x_5867_, 7, v___x_5866_);
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 4) as u32,
                        v___x_5865_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 5) as u32,
                        v___x_5865_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 6) as u32,
                        v___x_5865_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 7) as u32,
                        v___x_5865_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 8) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 9) as u32,
                        v___x_5865_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5867_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 10) as u32,
                        v_isZero_5858_,
                    );
                    v___x_5868_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6;
                    v___x_5869_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                        v___x_5861_,
                        v___x_5867_,
                        v___x_5868_,
                        v_a_5845_,
                        v_a_5846_,
                        v_a_5847_,
                        v_a_5848_,
                    );
                    if lean_obj_tag(v___x_5869_) == 0 {
                        v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
                        v_isSharedCheck_5881_ = (!lean_is_exclusive(v___x_5869_)) as u8;
                        if v_isSharedCheck_5881_ == 0 {
                            v___x_5872_ = v___x_5869_;
                            v_isShared_5873_ = v_isSharedCheck_5881_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5870_);
                            lean_dec(v___x_5869_);
                            v___x_5872_ = lean_box(0);
                            v_isShared_5873_ = v_isSharedCheck_5881_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5882_ = lean_ctor_get(v___x_5869_, 0);
                        v_isSharedCheck_5889_ = (!lean_is_exclusive(v___x_5869_)) as u8;
                        if v_isSharedCheck_5889_ == 0 {
                            v___x_5884_ = v___x_5869_;
                            v_isShared_5885_ = v_isSharedCheck_5889_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5882_);
                            lean_dec(v___x_5869_);
                            v___x_5884_ = lean_box(0);
                            v_isShared_5885_ = v_isSharedCheck_5889_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_5890_ = lean_box((v_isZero_5858_) as usize);
                    v___f_5891_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_5891_, 0, v___x_5890_);
                    v___x_5892_ = lean_box((v_isZero_5858_) as usize);
                    v___f_5893_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__2___boxed as *mut core::ffi::c_void, 10, 1);
                    lean_closure_set(v___f_5893_, 0, v___x_5892_);
                    v___x_5894_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                        9,
                        2,
                    );
                    lean_closure_set(v___x_5894_, 0, v_mvar_5843_);
                    lean_closure_set(v___x_5894_, 1, v___f_5893_);
                    v___x_5895_ = lean_box(0);
                    v___x_5896_ = lean_box(0);
                    v___x_5897_ = 1;
                    v___x_5898_ = lean_box(1);
                    v___x_5899_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__4;
                    v___x_5900_ = lean_alloc_ctor(0, 8, (11) as u32);
                    lean_ctor_set(v___x_5900_, 0, v___x_5895_);
                    lean_ctor_set(v___x_5900_, 1, v___x_5896_);
                    lean_ctor_set(v___x_5900_, 2, v___x_5895_);
                    lean_ctor_set(v___x_5900_, 3, v___f_5891_);
                    lean_ctor_set(v___x_5900_, 4, v___x_5898_);
                    lean_ctor_set(v___x_5900_, 5, v___x_5898_);
                    lean_ctor_set(v___x_5900_, 6, v___x_5895_);
                    lean_ctor_set(v___x_5900_, 7, v___x_5899_);
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                        v___x_5897_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 1) as u32,
                        v___x_5897_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                        v___x_5897_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 3) as u32,
                        v___x_5897_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 4) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 5) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 6) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 7) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 8) as u32,
                        v___x_5897_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 9) as u32,
                        v_isZero_5858_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5900_,
                        (core::mem::size_of::<*mut LeanObject>() * 8 + 10) as u32,
                        v___x_5897_,
                    );
                    v___x_5901_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__6;
                    lean_inc_ref(v___x_5900_);
                    v___x_5902_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                        v___x_5894_,
                        v___x_5900_,
                        v___x_5901_,
                        v_a_5845_,
                        v_a_5846_,
                        v_a_5847_,
                        v_a_5848_,
                    );
                    if lean_obj_tag(v___x_5902_) == 0 {
                        v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
                        lean_inc(v_a_5903_);
                        lean_dec_ref_known(v___x_5902_, 1);
                        v_fst_5904_ = lean_ctor_get(v_a_5903_, 0);
                        lean_inc(v_fst_5904_);
                        lean_dec(v_a_5903_);
                        if lean_obj_tag(v_fst_5904_) == 1 {
                            v_tail_5905_ = lean_ctor_get(v_fst_5904_, 1);
                            lean_inc(v_tail_5905_);
                            if lean_obj_tag(v_tail_5905_) == 1 {
                                v_tail_5906_ = lean_ctor_get(v_tail_5905_, 1);
                                if lean_obj_tag(v_tail_5906_) == 0 {
                                    v_head_5907_ = lean_ctor_get(v_fst_5904_, 0);
                                    lean_inc(v_head_5907_);
                                    lean_dec_ref_known(v_fst_5904_, 2);
                                    v_head_5908_ = lean_ctor_get(v_tail_5905_, 0);
                                    lean_inc(v_head_5908_);
                                    lean_dec_ref_known(v_tail_5905_, 2);
                                    v___x_5909_ = lean_box((v_isZero_5858_) as usize);
                                    v___f_5910_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___lam__3___boxed as *mut core::ffi::c_void, 10, 1);
                                    lean_closure_set(v___f_5910_, 0, v___x_5909_);
                                    v___x_5911_ = lean_alloc_closure(
                                        l_Lean_Elab_Tactic_run___boxed as *mut core::ffi::c_void,
                                        9,
                                        2,
                                    );
                                    lean_closure_set(v___x_5911_, 0, v_head_5907_);
                                    lean_closure_set(v___x_5911_, 1, v___f_5910_);
                                    v___x_5912_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                                        v___x_5911_,
                                        v___x_5900_,
                                        v___x_5901_,
                                        v_a_5845_,
                                        v_a_5846_,
                                        v_a_5847_,
                                        v_a_5848_,
                                    );
                                    if lean_obj_tag(v___x_5912_) == 0 {
                                        v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
                                        lean_inc(v_a_5913_);
                                        lean_dec_ref_known(v___x_5912_, 1);
                                        v_fst_5914_ = lean_ctor_get(v_a_5913_, 0);
                                        lean_inc(v_fst_5914_);
                                        lean_dec(v_a_5913_);
                                        if lean_obj_tag(v_fst_5914_) == 0 {
                                            v_one_5915_ = lean_unsigned_to_nat(1);
                                            v_n_5916_ = lean_nat_sub(v_n_5844_, v_one_5915_);
                                            lean_dec(v_n_5844_);
                                            v_mvar_5843_ = v_head_5908_;
                                            v_n_5844_ = v_n_5916_;
                                            state = 0;
                                            continue;
                                        } else {
                                            lean_dec(v_fst_5914_);
                                            lean_dec(v_head_5908_);
                                            lean_dec(v_n_5844_);
                                            v___x_5918_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
                                            v___x_5919_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_5918_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_);
                                            return v___x_5919_;
                                        }
                                    } else {
                                        lean_dec(v_head_5908_);
                                        lean_dec(v_n_5844_);
                                        v_a_5920_ = lean_ctor_get(v___x_5912_, 0);
                                        v_isSharedCheck_5927_ =
                                            (!lean_is_exclusive(v___x_5912_)) as u8;
                                        if v_isSharedCheck_5927_ == 0 {
                                            v___x_5922_ = v___x_5912_;
                                            v_isShared_5923_ = v_isSharedCheck_5927_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5920_);
                                            lean_dec(v___x_5912_);
                                            v___x_5922_ = lean_box(0);
                                            v_isShared_5923_ = v_isSharedCheck_5927_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_tail_5905_, 2);
                                    lean_dec_ref_known(v_fst_5904_, 2);
                                    lean_dec_ref_known(v___x_5900_, 8);
                                    lean_dec(v_n_5844_);
                                    v___y_5851_ = v_a_5845_;
                                    v___y_5852_ = v_a_5846_;
                                    v___y_5853_ = v_a_5847_;
                                    v___y_5854_ = v_a_5848_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_tail_5905_);
                                lean_dec_ref_known(v_fst_5904_, 2);
                                lean_dec_ref_known(v___x_5900_, 8);
                                lean_dec(v_n_5844_);
                                v___y_5851_ = v_a_5845_;
                                v___y_5852_ = v_a_5846_;
                                v___y_5853_ = v_a_5847_;
                                v___y_5854_ = v_a_5848_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_5904_);
                            lean_dec_ref_known(v___x_5900_, 8);
                            lean_dec(v_n_5844_);
                            v___y_5851_ = v_a_5845_;
                            v___y_5852_ = v_a_5846_;
                            v___y_5853_ = v_a_5847_;
                            v___y_5854_ = v_a_5848_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_5900_, 8);
                        lean_dec(v_n_5844_);
                        v_a_5928_ = lean_ctor_get(v___x_5902_, 0);
                        v_isSharedCheck_5935_ = (!lean_is_exclusive(v___x_5902_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5902_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5928_);
                            lean_dec(v___x_5902_);
                            v___x_5930_ = lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5855_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1), core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1_once), _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2___closed__1);
                v___x_5856_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_5855_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
                return v___x_5856_;
            }
            2 => {
                v_fst_5874_ = lean_ctor_get(v_a_5870_, 0);
                lean_inc(v_fst_5874_);
                lean_dec(v_a_5870_);
                if lean_obj_tag(v_fst_5874_) == 0 {
                    v___x_5875_ = lean_box(0);
                    if v_isShared_5873_ == 0 {
                        lean_ctor_set(v___x_5872_, 0, v___x_5875_);
                        v___x_5877_ = v___x_5872_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5878_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5878_, 0, v___x_5875_);
                        v___x_5877_ = v_reuseFailAlloc_5878_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_5874_);
                    lean_del_object(v___x_5872_);
                    v___x_5879_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___closed__2);
                    v___x_5880_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_5879_, v_a_5845_, v_a_5846_, v_a_5847_, v_a_5848_);
                    return v___x_5880_;
                }
            }
            3 => {
                return v___x_5877_;
            }
            4 => {
                if v_isShared_5885_ == 0 {
                    v___x_5887_ = v___x_5884_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
                    v___x_5887_ = v_reuseFailAlloc_5888_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5887_;
            }
            6 => {
                if v_isShared_5923_ == 0 {
                    v___x_5925_ = v___x_5922_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_a_5920_);
                    v___x_5925_ = v_reuseFailAlloc_5926_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5925_;
            }
            8 => {
                if v_isShared_5931_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor___boxed(
    mut v_mvar_5936_: *mut LeanObject,
    mut v_n_5937_: *mut LeanObject,
    mut v_a_5938_: *mut LeanObject,
    mut v_a_5939_: *mut LeanObject,
    mut v_a_5940_: *mut LeanObject,
    mut v_a_5941_: *mut LeanObject,
    mut v_a_5942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5943_: *mut LeanObject = core::ptr::null_mut();
    v_res_5943_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(
        v_mvar_5936_,
        v_n_5937_,
        v_a_5938_,
        v_a_5939_,
        v_a_5940_,
        v_a_5941_,
    );
    lean_dec(v_a_5941_);
    lean_dec_ref(v_a_5940_);
    lean_dec(v_a_5939_);
    lean_dec_ref(v_a_5938_);
    return v_res_5943_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(
    mut v_a_5944_: *mut LeanObject,
    mut v_a_5945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v_tail_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5944_) == 0 {
                    v___x_5946_ = lean_array_to_list(v_a_5945_);
                    return v___x_5946_;
                } else {
                    v_head_5947_ = lean_ctor_get(v_a_5944_, 0);
                    v_fst_5948_ = lean_ctor_get(v_head_5947_, 0);
                    v___x_5949_ = (lean_unbox(v_fst_5948_) as u8);
                    if v___x_5949_ == 0 {
                        v_tail_5950_ = lean_ctor_get(v_a_5944_, 1);
                        lean_inc(v_tail_5950_);
                        lean_dec_ref_known(v_a_5944_, 2);
                        v_a_5944_ = v_tail_5950_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_5947_);
                        v_tail_5952_ = lean_ctor_get(v_a_5944_, 1);
                        lean_inc(v_tail_5952_);
                        lean_dec_ref_known(v_a_5944_, 2);
                        v_snd_5953_ = lean_ctor_get(v_head_5947_, 1);
                        lean_inc(v_snd_5953_);
                        lean_dec(v_head_5947_);
                        v___x_5954_ = lean_array_push(v_a_5945_, v_snd_5953_);
                        v_a_5944_ = v_tail_5952_;
                        v_a_5945_ = v___x_5954_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(
    mut v_a_5956_: *mut LeanObject,
    mut v_x_5957_: *mut LeanObject,
    mut v_x_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
    mut v___y_5961_: *mut LeanObject,
    mut v___y_5962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5970_: u8 = 0;
    let mut v___y_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5981_: u8 = 0;
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5985_: u8 = 0;
    let mut v_fst_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_variablesKept_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neqs_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6015_: u8 = 0;
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6019_: u8 = 0;
    let mut v_val_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6028_: u8 = 0;
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6032_: u8 = 0;
    let mut v_a_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6040_: u8 = 0;
    let mut v_isSharedCheck_6041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5957_) == 0 {
                    v___x_5964_ = l_List_reverse___redArg(v_x_5958_);
                    v___x_5965_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5965_, 0, v___x_5964_);
                    return v___x_5965_;
                } else {
                    v_head_5966_ = lean_ctor_get(v_x_5957_, 0);
                    v_tail_5967_ = lean_ctor_get(v_x_5957_, 1);
                    v_isSharedCheck_6041_ = (!lean_is_exclusive(v_x_5957_)) as u8;
                    if v_isSharedCheck_6041_ == 0 {
                        v___x_5969_ = v_x_5957_;
                        v_isShared_5970_ = v_isSharedCheck_6041_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5967_);
                        lean_inc(v_head_5966_);
                        lean_dec(v_x_5957_);
                        v___x_5969_ = lean_box(0);
                        v_isShared_5970_ = v_isSharedCheck_6041_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5986_ = lean_ctor_get(v_head_5966_, 0);
                v_fst_5987_ = lean_ctor_get(v_fst_5986_, 0);
                lean_inc(v_fst_5987_);
                v_snd_5988_ = lean_ctor_get(v_fst_5986_, 1);
                v_toInductionSubgoal_5989_ = lean_ctor_get(v_snd_5988_, 0);
                lean_inc_ref(v_toInductionSubgoal_5989_);
                v_snd_5990_ = lean_ctor_get(v_head_5966_, 1);
                lean_inc(v_snd_5990_);
                lean_dec(v_head_5966_);
                v_variablesKept_5991_ = lean_ctor_get(v_fst_5987_, 0);
                lean_inc(v_variablesKept_5991_);
                v_neqs_5992_ = lean_ctor_get(v_fst_5987_, 1);
                lean_inc(v_neqs_5992_);
                lean_dec(v_fst_5987_);
                v_mvarId_5993_ = lean_ctor_get(v_toInductionSubgoal_5989_, 0);
                lean_inc(v_mvarId_5993_);
                v_fields_5994_ = lean_ctor_get(v_toInductionSubgoal_5989_, 1);
                lean_inc_ref(v_fields_5994_);
                lean_dec_ref(v_toInductionSubgoal_5989_);
                v___x_5995_ = lean_array_get_size(v_a_5956_);
                v___x_5996_ = lean_unsigned_to_nat(1);
                v___x_5997_ = lean_nat_sub(v___x_5995_, v___x_5996_);
                v___x_5998_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_select(
                    v_snd_5990_,
                    v___x_5997_,
                    v_mvarId_5993_,
                    v___y_5959_,
                    v___y_5960_,
                    v___y_5961_,
                    v___y_5962_,
                );
                if lean_obj_tag(v___x_5998_) == 0 {
                    v_a_5999_ = lean_ctor_get(v___x_5998_, 0);
                    lean_inc(v_a_5999_);
                    lean_dec_ref_known(v___x_5998_, 1);
                    lean_inc_ref(v_fields_5994_);
                    v___x_6000_ = lean_array_to_list(v_fields_5994_);
                    lean_inc(v_variablesKept_5991_);
                    v___x_6001_ = l_List_zipWith___at___00List_zip_spec__0(
                        lean_box(0),
                        lean_box(0),
                        v_variablesKept_5991_,
                        v___x_6000_,
                    );
                    v___x_6002_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1;
                    v___x_6003_ = l_List_filterMapTR_go___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__0(v___x_6001_, v___x_6002_);
                    if lean_obj_tag(v_neqs_5992_) == 0 {
                        v___x_6004_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_List_init___redArg(v___x_6003_);
                        v___x_6005_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_5999_, v___x_6004_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
                        if lean_obj_tag(v___x_6005_) == 0 {
                            v_a_6006_ = lean_ctor_get(v___x_6005_, 0);
                            lean_inc(v_a_6006_);
                            lean_dec_ref_known(v___x_6005_, 1);
                            v___x_6007_ = l_Lean_instInhabitedExpr;
                            v___x_6008_ = l_List_lengthTR___redArg(v_variablesKept_5991_);
                            lean_dec(v_variablesKept_5991_);
                            v___x_6009_ = lean_nat_sub(v___x_6008_, v___x_5996_);
                            lean_dec(v___x_6008_);
                            v___x_6010_ = lean_array_get(v___x_6007_, v_fields_5994_, v___x_6009_);
                            lean_dec(v___x_6009_);
                            lean_dec_ref(v_fields_5994_);
                            v___x_6011_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_a_6006_, v___x_6010_, v___y_5960_);
                            v___y_5972_ = v___x_6011_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec_ref(v_fields_5994_);
                            lean_dec(v_variablesKept_5991_);
                            lean_del_object(v___x_5969_);
                            lean_dec(v_tail_5967_);
                            lean_dec(v_x_5958_);
                            v_a_6012_ = lean_ctor_get(v___x_6005_, 0);
                            v_isSharedCheck_6019_ = (!lean_is_exclusive(v___x_6005_)) as u8;
                            if v_isSharedCheck_6019_ == 0 {
                                v___x_6014_ = v___x_6005_;
                                v_isShared_6015_ = v_isSharedCheck_6019_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6012_);
                                lean_dec(v___x_6005_);
                                v___x_6014_ = lean_box(0);
                                v_isShared_6015_ = v_isSharedCheck_6019_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_fields_5994_);
                        lean_dec(v_variablesKept_5991_);
                        v_val_6020_ = lean_ctor_get(v_neqs_5992_, 0);
                        lean_inc(v_val_6020_);
                        lean_dec_ref_known(v_neqs_5992_, 1);
                        v___x_6021_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__2(v_a_5999_, v___x_6003_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
                        if lean_obj_tag(v___x_6021_) == 0 {
                            v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
                            lean_inc(v_a_6022_);
                            lean_dec_ref_known(v___x_6021_, 1);
                            v___x_6023_ = lean_nat_sub(v_val_6020_, v___x_5996_);
                            lean_dec(v_val_6020_);
                            v___x_6024_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_splitThenConstructor(v_a_6022_, v___x_6023_, v___y_5959_, v___y_5960_, v___y_5961_, v___y_5962_);
                            v___y_5972_ = v___x_6024_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_val_6020_);
                            lean_del_object(v___x_5969_);
                            lean_dec(v_tail_5967_);
                            lean_dec(v_x_5958_);
                            v_a_6025_ = lean_ctor_get(v___x_6021_, 0);
                            v_isSharedCheck_6032_ = (!lean_is_exclusive(v___x_6021_)) as u8;
                            if v_isSharedCheck_6032_ == 0 {
                                v___x_6027_ = v___x_6021_;
                                v_isShared_6028_ = v_isSharedCheck_6032_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_6025_);
                                lean_dec(v___x_6021_);
                                v___x_6027_ = lean_box(0);
                                v_isShared_6028_ = v_isSharedCheck_6032_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_fields_5994_);
                    lean_dec(v_neqs_5992_);
                    lean_dec(v_variablesKept_5991_);
                    lean_del_object(v___x_5969_);
                    lean_dec(v_tail_5967_);
                    lean_dec(v_x_5958_);
                    v_a_6033_ = lean_ctor_get(v___x_5998_, 0);
                    v_isSharedCheck_6040_ = (!lean_is_exclusive(v___x_5998_)) as u8;
                    if v_isSharedCheck_6040_ == 0 {
                        v___x_6035_ = v___x_5998_;
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6033_);
                        lean_dec(v___x_5998_);
                        v___x_6035_ = lean_box(0);
                        v_isShared_6036_ = v_isSharedCheck_6040_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v___y_5972_) == 0 {
                    v_a_5973_ = lean_ctor_get(v___y_5972_, 0);
                    lean_inc(v_a_5973_);
                    lean_dec_ref_known(v___y_5972_, 1);
                    if v_isShared_5970_ == 0 {
                        lean_ctor_set(v___x_5969_, 1, v_x_5958_);
                        lean_ctor_set(v___x_5969_, 0, v_a_5973_);
                        v___x_5975_ = v___x_5969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5977_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5977_, 0, v_a_5973_);
                        lean_ctor_set(v_reuseFailAlloc_5977_, 1, v_x_5958_);
                        v___x_5975_ = v_reuseFailAlloc_5977_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5969_);
                    lean_dec(v_tail_5967_);
                    lean_dec(v_x_5958_);
                    v_a_5978_ = lean_ctor_get(v___y_5972_, 0);
                    v_isSharedCheck_5985_ = (!lean_is_exclusive(v___y_5972_)) as u8;
                    if v_isSharedCheck_5985_ == 0 {
                        v___x_5980_ = v___y_5972_;
                        v_isShared_5981_ = v_isSharedCheck_5985_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5978_);
                        lean_dec(v___y_5972_);
                        v___x_5980_ = lean_box(0);
                        v_isShared_5981_ = v_isSharedCheck_5985_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_x_5957_ = v_tail_5967_;
                v_x_5958_ = v___x_5975_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_5981_ == 0 {
                    v___x_5983_ = v___x_5980_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5984_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_a_5978_);
                    v___x_5983_ = v_reuseFailAlloc_5984_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5983_;
            }
            6 => {
                if v_isShared_6015_ == 0 {
                    v___x_6017_ = v___x_6014_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
                    v___x_6017_ = v_reuseFailAlloc_6018_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6017_;
            }
            8 => {
                if v_isShared_6028_ == 0 {
                    v___x_6030_ = v___x_6027_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6031_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6031_, 0, v_a_6025_);
                    v___x_6030_ = v_reuseFailAlloc_6031_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6030_;
            }
            10 => {
                if v_isShared_6036_ == 0 {
                    v___x_6038_ = v___x_6035_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6039_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
                    v___x_6038_ = v_reuseFailAlloc_6039_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1___boxed(
    mut v_a_6042_: *mut LeanObject,
    mut v_x_6043_: *mut LeanObject,
    mut v_x_6044_: *mut LeanObject,
    mut v___y_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
    mut v___y_6047_: *mut LeanObject,
    mut v___y_6048_: *mut LeanObject,
    mut v___y_6049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6050_: *mut LeanObject = core::ptr::null_mut();
    v_res_6050_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_6042_, v_x_6043_, v_x_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_);
    lean_dec(v___y_6048_);
    lean_dec_ref(v___y_6047_);
    lean_dec(v___y_6046_);
    lean_dec_ref(v___y_6045_);
    lean_dec_ref(v_a_6042_);
    return v_res_6050_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(
    mut v_mvar_6053_: *mut LeanObject,
    mut v_shape_6054_: *mut LeanObject,
    mut v_a_6055_: *mut LeanObject,
    mut v_a_6056_: *mut LeanObject,
    mut v_a_6057_: *mut LeanObject,
    mut v_a_6058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6060_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6077_: u8 = 0;
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6082_: u8 = 0;
    let mut v_unused_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6087_: u8 = 0;
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6091_: u8 = 0;
    let mut v_a_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_a_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6103_: u8 = 0;
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6060_ = 0;
                v___x_6061_ = l_Lean_Meta_intro1Core(
                    v_mvar_6053_,
                    v___x_6060_,
                    v_a_6055_,
                    v_a_6056_,
                    v_a_6057_,
                    v_a_6058_,
                );
                if lean_obj_tag(v___x_6061_) == 0 {
                    v_a_6062_ = lean_ctor_get(v___x_6061_, 0);
                    lean_inc(v_a_6062_);
                    lean_dec_ref_known(v___x_6061_, 1);
                    v_fst_6063_ = lean_ctor_get(v_a_6062_, 0);
                    lean_inc(v_fst_6063_);
                    v_snd_6064_ = lean_ctor_get(v_a_6062_, 1);
                    lean_inc(v_snd_6064_);
                    lean_dec(v_a_6062_);
                    v___x_6065_ = lean_unsigned_to_nat(0);
                    v___x_6066_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0;
                    v___x_6067_ = lean_box(0);
                    v___x_6068_ = l_Lean_MVarId_cases(
                        v_snd_6064_,
                        v_fst_6063_,
                        v___x_6066_,
                        v___x_6060_,
                        v___x_6067_,
                        v_a_6055_,
                        v_a_6056_,
                        v_a_6057_,
                        v_a_6058_,
                    );
                    if lean_obj_tag(v___x_6068_) == 0 {
                        v_a_6069_ = lean_ctor_get(v___x_6068_, 0);
                        lean_inc_n(v_a_6069_, 2);
                        lean_dec_ref_known(v___x_6068_, 1);
                        v___x_6070_ = lean_array_to_list(v_a_6069_);
                        v___x_6071_ = l_List_zipWith___at___00List_zip_spec__0(
                            lean_box(0),
                            lean_box(0),
                            v_shape_6054_,
                            v___x_6070_,
                        );
                        v___x_6072_ = l_List_zipIdxTR___redArg(v___x_6071_, v___x_6065_);
                        v___x_6073_ = lean_box(0);
                        v___x_6074_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases_spec__1(v_a_6069_, v___x_6072_, v___x_6073_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_);
                        lean_dec(v_a_6069_);
                        if lean_obj_tag(v___x_6074_) == 0 {
                            v_isSharedCheck_6082_ = (!lean_is_exclusive(v___x_6074_)) as u8;
                            if v_isSharedCheck_6082_ == 0 {
                                v_unused_6083_ = lean_ctor_get(v___x_6074_, 0);
                                lean_dec(v_unused_6083_);
                                v___x_6076_ = v___x_6074_;
                                v_isShared_6077_ = v_isSharedCheck_6082_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_6074_);
                                v___x_6076_ = lean_box(0);
                                v_isShared_6077_ = v_isSharedCheck_6082_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6084_ = lean_ctor_get(v___x_6074_, 0);
                            v_isSharedCheck_6091_ = (!lean_is_exclusive(v___x_6074_)) as u8;
                            if v_isSharedCheck_6091_ == 0 {
                                v___x_6086_ = v___x_6074_;
                                v_isShared_6087_ = v_isSharedCheck_6091_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6084_);
                                lean_dec(v___x_6074_);
                                v___x_6086_ = lean_box(0);
                                v_isShared_6087_ = v_isSharedCheck_6091_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_shape_6054_);
                        v_a_6092_ = lean_ctor_get(v___x_6068_, 0);
                        v_isSharedCheck_6099_ = (!lean_is_exclusive(v___x_6068_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v___x_6094_ = v___x_6068_;
                            v_isShared_6095_ = v_isSharedCheck_6099_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_6092_);
                            lean_dec(v___x_6068_);
                            v___x_6094_ = lean_box(0);
                            v_isShared_6095_ = v_isSharedCheck_6099_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_shape_6054_);
                    v_a_6100_ = lean_ctor_get(v___x_6061_, 0);
                    v_isSharedCheck_6107_ = (!lean_is_exclusive(v___x_6061_)) as u8;
                    if v_isSharedCheck_6107_ == 0 {
                        v___x_6102_ = v___x_6061_;
                        v_isShared_6103_ = v_isSharedCheck_6107_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6100_);
                        lean_dec(v___x_6061_);
                        v___x_6102_ = lean_box(0);
                        v_isShared_6103_ = v_isSharedCheck_6107_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6078_ = lean_box(0);
                if v_isShared_6077_ == 0 {
                    lean_ctor_set(v___x_6076_, 0, v___x_6078_);
                    v___x_6080_ = v___x_6076_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6081_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6081_, 0, v___x_6078_);
                    v___x_6080_ = v_reuseFailAlloc_6081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6080_;
            }
            3 => {
                if v_isShared_6087_ == 0 {
                    v___x_6089_ = v___x_6086_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6084_);
                    v___x_6089_ = v_reuseFailAlloc_6090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6089_;
            }
            5 => {
                if v_isShared_6095_ == 0 {
                    v___x_6097_ = v___x_6094_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6097_;
            }
            7 => {
                if v_isShared_6103_ == 0 {
                    v___x_6105_ = v___x_6102_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
                    v___x_6105_ = v_reuseFailAlloc_6106_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___boxed(
    mut v_mvar_6108_: *mut LeanObject,
    mut v_shape_6109_: *mut LeanObject,
    mut v_a_6110_: *mut LeanObject,
    mut v_a_6111_: *mut LeanObject,
    mut v_a_6112_: *mut LeanObject,
    mut v_a_6113_: *mut LeanObject,
    mut v_a_6114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6115_: *mut LeanObject = core::ptr::null_mut();
    v_res_6115_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(
        v_mvar_6108_,
        v_shape_6109_,
        v_a_6110_,
        v_a_6111_,
        v_a_6112_,
        v_a_6113_,
    );
    lean_dec(v_a_6113_);
    lean_dec_ref(v_a_6112_);
    lean_dec(v_a_6111_);
    lean_dec_ref(v_a_6110_);
    return v_res_6115_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1()
-> *mut LeanObject {
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    v___x_6117_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__0;
    v___x_6118_ = l_Lean_stringToMessageData(v___x_6117_);
    return v___x_6118_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3()
-> *mut LeanObject {
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    v___x_6120_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__2;
    v___x_6121_ = l_Lean_stringToMessageData(v___x_6120_);
    return v___x_6121_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(
    mut v_n_6122_: *mut LeanObject,
    mut v_mvar_6123_: *mut LeanObject,
    mut v_h_6124_: *mut LeanObject,
    mut v_a_6125_: *mut LeanObject,
    mut v_a_6126_: *mut LeanObject,
    mut v_a_6127_: *mut LeanObject,
    mut v_a_6128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6145_: u8 = 0;
    let mut v___x_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: u8 = 0;
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v_mvarId_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: u8 = 0;
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6175_: u8 = 0;
    let mut v_mvarId_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: u8 = 0;
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6197_: u8 = 0;
    let mut v_isSharedCheck_6198_: u8 = 0;
    let mut v_unused_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6200_: u8 = 0;
    let mut v_unused_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6209_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6144_ = lean_unsigned_to_nat(0);
                v_isZero_6145_ = lean_nat_dec_eq(v_n_6122_, v_zero_6144_);
                if v_isZero_6145_ == 1 {
                    v___x_6146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6146_, 0, v_h_6124_);
                    lean_ctor_set(v___x_6146_, 1, v_mvar_6123_);
                    v___x_6147_ = lean_box(0);
                    v___x_6148_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6148_, 0, v___x_6146_);
                    lean_ctor_set(v___x_6148_, 1, v___x_6147_);
                    v___x_6149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6149_, 0, v___x_6148_);
                    return v___x_6149_;
                } else {
                    v___x_6150_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0;
                    v___x_6151_ = lean_box(0);
                    v___x_6152_ = l_Lean_MVarId_cases(
                        v_mvar_6123_,
                        v_h_6124_,
                        v___x_6150_,
                        v_isZero_6145_,
                        v___x_6151_,
                        v_a_6125_,
                        v_a_6126_,
                        v_a_6127_,
                        v_a_6128_,
                    );
                    if lean_obj_tag(v___x_6152_) == 0 {
                        v_a_6153_ = lean_ctor_get(v___x_6152_, 0);
                        lean_inc(v_a_6153_);
                        lean_dec_ref_known(v___x_6152_, 1);
                        v___x_6154_ = lean_array_get_size(v_a_6153_);
                        v___x_6155_ = lean_unsigned_to_nat(2);
                        v___x_6156_ = lean_nat_dec_eq(v___x_6154_, v___x_6155_);
                        if v___x_6156_ == 0 {
                            lean_dec(v_a_6153_);
                            v___x_6157_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__3);
                            v___x_6158_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6157_, v_a_6125_, v_a_6126_, v_a_6127_, v_a_6128_);
                            return v___x_6158_;
                        } else {
                            v___x_6159_ = lean_array_fget(v_a_6153_, v_zero_6144_);
                            v_toInductionSubgoal_6160_ = lean_ctor_get(v___x_6159_, 0);
                            v_isSharedCheck_6200_ = (!lean_is_exclusive(v___x_6159_)) as u8;
                            if v_isSharedCheck_6200_ == 0 {
                                v_unused_6201_ = lean_ctor_get(v___x_6159_, 1);
                                lean_dec(v_unused_6201_);
                                v___x_6162_ = v___x_6159_;
                                v_isShared_6163_ = v_isSharedCheck_6200_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_toInductionSubgoal_6160_);
                                lean_dec(v___x_6159_);
                                v___x_6162_ = lean_box(0);
                                v_isShared_6163_ = v_isSharedCheck_6200_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_6202_ = lean_ctor_get(v___x_6152_, 0);
                        v_isSharedCheck_6209_ = (!lean_is_exclusive(v___x_6152_)) as u8;
                        if v_isSharedCheck_6209_ == 0 {
                            v___x_6204_ = v___x_6152_;
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6202_);
                            lean_dec(v___x_6152_);
                            v___x_6204_ = lean_box(0);
                            v_isShared_6205_ = v_isSharedCheck_6209_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6135_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
                v___x_6136_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6135_, v___y_6131_, v___y_6132_, v___y_6133_, v___y_6134_);
                return v___x_6136_;
            }
            2 => {
                v___x_6142_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
                v___x_6143_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6142_, v___y_6138_, v___y_6139_, v___y_6140_, v___y_6141_);
                return v___x_6143_;
            }
            3 => {
                v_mvarId_6164_ = lean_ctor_get(v_toInductionSubgoal_6160_, 0);
                lean_inc(v_mvarId_6164_);
                v_fields_6165_ = lean_ctor_get(v_toInductionSubgoal_6160_, 1);
                lean_inc_ref(v_fields_6165_);
                lean_dec_ref(v_toInductionSubgoal_6160_);
                v___x_6166_ = lean_array_get_size(v_fields_6165_);
                v___x_6167_ = lean_unsigned_to_nat(1);
                v___x_6168_ = lean_nat_dec_eq(v___x_6166_, v___x_6167_);
                if v___x_6168_ == 0 {
                    lean_dec_ref(v_fields_6165_);
                    lean_dec(v_mvarId_6164_);
                    lean_del_object(v___x_6162_);
                    lean_dec(v_a_6153_);
                    v___y_6131_ = v_a_6125_;
                    v___y_6132_ = v_a_6126_;
                    v___y_6133_ = v_a_6127_;
                    v___y_6134_ = v_a_6128_;
                    state = 1;
                    continue;
                } else {
                    v___x_6169_ = lean_array_fget(v_fields_6165_, v_zero_6144_);
                    lean_dec_ref(v_fields_6165_);
                    if lean_obj_tag(v___x_6169_) == 1 {
                        v_fvarId_6170_ = lean_ctor_get(v___x_6169_, 0);
                        lean_inc(v_fvarId_6170_);
                        lean_dec_ref_known(v___x_6169_, 1);
                        v___x_6171_ = lean_array_fget(v_a_6153_, v___x_6167_);
                        lean_dec(v_a_6153_);
                        v_toInductionSubgoal_6172_ = lean_ctor_get(v___x_6171_, 0);
                        v_isSharedCheck_6198_ = (!lean_is_exclusive(v___x_6171_)) as u8;
                        if v_isSharedCheck_6198_ == 0 {
                            v_unused_6199_ = lean_ctor_get(v___x_6171_, 1);
                            lean_dec(v_unused_6199_);
                            v___x_6174_ = v___x_6171_;
                            v_isShared_6175_ = v_isSharedCheck_6198_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_toInductionSubgoal_6172_);
                            lean_dec(v___x_6171_);
                            v___x_6174_ = lean_box(0);
                            v_isShared_6175_ = v_isSharedCheck_6198_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6169_);
                        lean_dec(v_mvarId_6164_);
                        lean_del_object(v___x_6162_);
                        lean_dec(v_a_6153_);
                        v___y_6131_ = v_a_6125_;
                        v___y_6132_ = v_a_6126_;
                        v___y_6133_ = v_a_6127_;
                        v___y_6134_ = v_a_6128_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v_mvarId_6176_ = lean_ctor_get(v_toInductionSubgoal_6172_, 0);
                lean_inc(v_mvarId_6176_);
                v_fields_6177_ = lean_ctor_get(v_toInductionSubgoal_6172_, 1);
                lean_inc_ref(v_fields_6177_);
                lean_dec_ref(v_toInductionSubgoal_6172_);
                v___x_6178_ = lean_array_get_size(v_fields_6177_);
                v___x_6179_ = lean_nat_dec_eq(v___x_6178_, v___x_6167_);
                if v___x_6179_ == 0 {
                    lean_dec_ref(v_fields_6177_);
                    lean_dec(v_mvarId_6176_);
                    lean_del_object(v___x_6174_);
                    lean_dec(v_fvarId_6170_);
                    lean_dec(v_mvarId_6164_);
                    lean_del_object(v___x_6162_);
                    v___y_6138_ = v_a_6125_;
                    v___y_6139_ = v_a_6126_;
                    v___y_6140_ = v_a_6127_;
                    v___y_6141_ = v_a_6128_;
                    state = 2;
                    continue;
                } else {
                    v___x_6180_ = lean_array_fget(v_fields_6177_, v_zero_6144_);
                    lean_dec_ref(v_fields_6177_);
                    if lean_obj_tag(v___x_6180_) == 1 {
                        v_fvarId_6181_ = lean_ctor_get(v___x_6180_, 0);
                        lean_inc(v_fvarId_6181_);
                        lean_dec_ref_known(v___x_6180_, 1);
                        v_n_6182_ = lean_nat_sub(v_n_6122_, v___x_6167_);
                        v___x_6183_ =
                            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(
                                v_n_6182_,
                                v_mvarId_6176_,
                                v_fvarId_6181_,
                                v_a_6125_,
                                v_a_6126_,
                                v_a_6127_,
                                v_a_6128_,
                            );
                        lean_dec(v_n_6182_);
                        if lean_obj_tag(v___x_6183_) == 0 {
                            v_a_6184_ = lean_ctor_get(v___x_6183_, 0);
                            v_isSharedCheck_6197_ = (!lean_is_exclusive(v___x_6183_)) as u8;
                            if v_isSharedCheck_6197_ == 0 {
                                v___x_6186_ = v___x_6183_;
                                v_isShared_6187_ = v_isSharedCheck_6197_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6184_);
                                lean_dec(v___x_6183_);
                                v___x_6186_ = lean_box(0);
                                v_isShared_6187_ = v_isSharedCheck_6197_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6174_);
                            lean_dec(v_fvarId_6170_);
                            lean_dec(v_mvarId_6164_);
                            lean_del_object(v___x_6162_);
                            return v___x_6183_;
                        }
                    } else {
                        lean_dec(v___x_6180_);
                        lean_dec(v_mvarId_6176_);
                        lean_del_object(v___x_6174_);
                        lean_dec(v_fvarId_6170_);
                        lean_dec(v_mvarId_6164_);
                        lean_del_object(v___x_6162_);
                        v___y_6138_ = v_a_6125_;
                        v___y_6139_ = v_a_6126_;
                        v___y_6140_ = v_a_6127_;
                        v___y_6141_ = v_a_6128_;
                        state = 2;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6175_ == 0 {
                    lean_ctor_set(v___x_6174_, 1, v_mvarId_6164_);
                    lean_ctor_set(v___x_6174_, 0, v_fvarId_6170_);
                    v___x_6189_ = v___x_6174_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6196_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_fvarId_6170_);
                    lean_ctor_set(v_reuseFailAlloc_6196_, 1, v_mvarId_6164_);
                    v___x_6189_ = v_reuseFailAlloc_6196_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6163_ == 0 {
                    lean_ctor_set_tag(v___x_6162_, 1);
                    lean_ctor_set(v___x_6162_, 1, v_a_6184_);
                    lean_ctor_set(v___x_6162_, 0, v___x_6189_);
                    v___x_6191_ = v___x_6162_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6195_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6195_, 0, v___x_6189_);
                    lean_ctor_set(v_reuseFailAlloc_6195_, 1, v_a_6184_);
                    v___x_6191_ = v_reuseFailAlloc_6195_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6187_ == 0 {
                    lean_ctor_set(v___x_6186_, 0, v___x_6191_);
                    v___x_6193_ = v___x_6186_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6194_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6194_, 0, v___x_6191_);
                    v___x_6193_ = v_reuseFailAlloc_6194_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6193_;
            }
            9 => {
                if v_isShared_6205_ == 0 {
                    v___x_6207_ = v___x_6204_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6208_, 0, v_a_6202_);
                    v___x_6207_ = v_reuseFailAlloc_6208_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___boxed(
    mut v_n_6210_: *mut LeanObject,
    mut v_mvar_6211_: *mut LeanObject,
    mut v_h_6212_: *mut LeanObject,
    mut v_a_6213_: *mut LeanObject,
    mut v_a_6214_: *mut LeanObject,
    mut v_a_6215_: *mut LeanObject,
    mut v_a_6216_: *mut LeanObject,
    mut v_a_6217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6218_: *mut LeanObject = core::ptr::null_mut();
    v_res_6218_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(
        v_n_6210_,
        v_mvar_6211_,
        v_h_6212_,
        v_a_6213_,
        v_a_6214_,
        v_a_6215_,
        v_a_6216_,
    );
    lean_dec(v_a_6216_);
    lean_dec_ref(v_a_6215_);
    lean_dec(v_a_6214_);
    lean_dec_ref(v_a_6213_);
    lean_dec(v_n_6210_);
    return v_res_6218_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1()
-> *mut LeanObject {
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut LeanObject = core::ptr::null_mut();
    v___x_6220_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__0;
    v___x_6221_ = l_Lean_stringToMessageData(v___x_6220_);
    return v___x_6221_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
    mut v_n_6222_: *mut LeanObject,
    mut v_mvar_6223_: *mut LeanObject,
    mut v_h_6224_: *mut LeanObject,
    mut v_a_6225_: *mut LeanObject,
    mut v_a_6226_: *mut LeanObject,
    mut v_a_6227_: *mut LeanObject,
    mut v_a_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6238_: u8 = 0;
    let mut v___x_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: u8 = 0;
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6256_: u8 = 0;
    let mut v_mvarId_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: u8 = 0;
    let mut v___x_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6271_: u8 = 0;
    let mut v_fst_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6276_: u8 = 0;
    let mut v___x_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_isSharedCheck_6287_: u8 = 0;
    let mut v_isSharedCheck_6288_: u8 = 0;
    let mut v_unused_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6293_: u8 = 0;
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_6237_ = lean_unsigned_to_nat(0);
                v_isZero_6238_ = lean_nat_dec_eq(v_n_6222_, v_zero_6237_);
                if v_isZero_6238_ == 1 {
                    v___x_6239_ = lean_box(0);
                    v___x_6240_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6240_, 0, v_h_6224_);
                    lean_ctor_set(v___x_6240_, 1, v___x_6239_);
                    v___x_6241_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6241_, 0, v_mvar_6223_);
                    lean_ctor_set(v___x_6241_, 1, v___x_6240_);
                    v___x_6242_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6242_, 0, v___x_6241_);
                    return v___x_6242_;
                } else {
                    v___x_6243_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0;
                    v___x_6244_ = lean_box(0);
                    v___x_6245_ = l_Lean_MVarId_cases(
                        v_mvar_6223_,
                        v_h_6224_,
                        v___x_6243_,
                        v_isZero_6238_,
                        v___x_6244_,
                        v_a_6225_,
                        v_a_6226_,
                        v_a_6227_,
                        v_a_6228_,
                    );
                    if lean_obj_tag(v___x_6245_) == 0 {
                        v_a_6246_ = lean_ctor_get(v___x_6245_, 0);
                        lean_inc(v_a_6246_);
                        lean_dec_ref_known(v___x_6245_, 1);
                        v___x_6247_ = lean_array_get_size(v_a_6246_);
                        v___x_6248_ = lean_unsigned_to_nat(1);
                        v___x_6249_ = lean_nat_dec_eq(v___x_6247_, v___x_6248_);
                        if v___x_6249_ == 0 {
                            lean_dec(v_a_6246_);
                            v___x_6250_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___closed__1);
                            v___x_6251_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6250_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_);
                            return v___x_6251_;
                        } else {
                            v___x_6252_ = lean_array_fget(v_a_6246_, v_zero_6237_);
                            lean_dec(v_a_6246_);
                            v_toInductionSubgoal_6253_ = lean_ctor_get(v___x_6252_, 0);
                            v_isSharedCheck_6288_ = (!lean_is_exclusive(v___x_6252_)) as u8;
                            if v_isSharedCheck_6288_ == 0 {
                                v_unused_6289_ = lean_ctor_get(v___x_6252_, 1);
                                lean_dec(v_unused_6289_);
                                v___x_6255_ = v___x_6252_;
                                v_isShared_6256_ = v_isSharedCheck_6288_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_toInductionSubgoal_6253_);
                                lean_dec(v___x_6252_);
                                v___x_6255_ = lean_box(0);
                                v_isShared_6256_ = v_isSharedCheck_6288_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_a_6290_ = lean_ctor_get(v___x_6245_, 0);
                        v_isSharedCheck_6297_ = (!lean_is_exclusive(v___x_6245_)) as u8;
                        if v_isSharedCheck_6297_ == 0 {
                            v___x_6292_ = v___x_6245_;
                            v_isShared_6293_ = v_isSharedCheck_6297_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6290_);
                            lean_dec(v___x_6245_);
                            v___x_6292_ = lean_box(0);
                            v_isShared_6293_ = v_isSharedCheck_6297_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6235_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum___closed__1);
                v___x_6236_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6235_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
                return v___x_6236_;
            }
            2 => {
                v_mvarId_6257_ = lean_ctor_get(v_toInductionSubgoal_6253_, 0);
                lean_inc(v_mvarId_6257_);
                v_fields_6258_ = lean_ctor_get(v_toInductionSubgoal_6253_, 1);
                lean_inc_ref(v_fields_6258_);
                lean_dec_ref(v_toInductionSubgoal_6253_);
                v___x_6259_ = lean_array_get_size(v_fields_6258_);
                v___x_6260_ = lean_unsigned_to_nat(2);
                v___x_6261_ = lean_nat_dec_eq(v___x_6259_, v___x_6260_);
                if v___x_6261_ == 0 {
                    lean_dec_ref(v_fields_6258_);
                    lean_dec(v_mvarId_6257_);
                    lean_del_object(v___x_6255_);
                    v___y_6231_ = v_a_6225_;
                    v___y_6232_ = v_a_6226_;
                    v___y_6233_ = v_a_6227_;
                    v___y_6234_ = v_a_6228_;
                    state = 1;
                    continue;
                } else {
                    v___x_6262_ = lean_array_fget_borrowed(v_fields_6258_, v_zero_6237_);
                    if lean_obj_tag(v___x_6262_) == 1 {
                        v_fvarId_6263_ = lean_ctor_get(v___x_6262_, 0);
                        lean_inc(v_fvarId_6263_);
                        v___x_6264_ = lean_array_fget(v_fields_6258_, v___x_6248_);
                        lean_dec_ref(v_fields_6258_);
                        if lean_obj_tag(v___x_6264_) == 1 {
                            v_fvarId_6265_ = lean_ctor_get(v___x_6264_, 0);
                            lean_inc(v_fvarId_6265_);
                            lean_dec_ref_known(v___x_6264_, 1);
                            v_n_6266_ = lean_nat_sub(v_n_6222_, v___x_6248_);
                            v___x_6267_ =
                                l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
                                    v_n_6266_,
                                    v_mvarId_6257_,
                                    v_fvarId_6265_,
                                    v_a_6225_,
                                    v_a_6226_,
                                    v_a_6227_,
                                    v_a_6228_,
                                );
                            lean_dec(v_n_6266_);
                            if lean_obj_tag(v___x_6267_) == 0 {
                                v_a_6268_ = lean_ctor_get(v___x_6267_, 0);
                                v_isSharedCheck_6287_ = (!lean_is_exclusive(v___x_6267_)) as u8;
                                if v_isSharedCheck_6287_ == 0 {
                                    v___x_6270_ = v___x_6267_;
                                    v_isShared_6271_ = v_isSharedCheck_6287_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6268_);
                                    lean_dec(v___x_6267_);
                                    v___x_6270_ = lean_box(0);
                                    v_isShared_6271_ = v_isSharedCheck_6287_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fvarId_6263_);
                                lean_del_object(v___x_6255_);
                                return v___x_6267_;
                            }
                        } else {
                            lean_dec(v___x_6264_);
                            lean_dec(v_fvarId_6263_);
                            lean_dec(v_mvarId_6257_);
                            lean_del_object(v___x_6255_);
                            v___y_6231_ = v_a_6225_;
                            v___y_6232_ = v_a_6226_;
                            v___y_6233_ = v_a_6227_;
                            v___y_6234_ = v_a_6228_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_fields_6258_);
                        lean_dec(v_mvarId_6257_);
                        lean_del_object(v___x_6255_);
                        v___y_6231_ = v_a_6225_;
                        v___y_6232_ = v_a_6226_;
                        v___y_6233_ = v_a_6227_;
                        v___y_6234_ = v_a_6228_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6272_ = lean_ctor_get(v_a_6268_, 0);
                v_snd_6273_ = lean_ctor_get(v_a_6268_, 1);
                v_isSharedCheck_6286_ = (!lean_is_exclusive(v_a_6268_)) as u8;
                if v_isSharedCheck_6286_ == 0 {
                    v___x_6275_ = v_a_6268_;
                    v_isShared_6276_ = v_isSharedCheck_6286_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_6273_);
                    lean_inc(v_fst_6272_);
                    lean_dec(v_a_6268_);
                    v___x_6275_ = lean_box(0);
                    v_isShared_6276_ = v_isSharedCheck_6286_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6256_ == 0 {
                    lean_ctor_set_tag(v___x_6255_, 1);
                    lean_ctor_set(v___x_6255_, 1, v_snd_6273_);
                    lean_ctor_set(v___x_6255_, 0, v_fvarId_6263_);
                    v___x_6278_ = v___x_6255_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_fvarId_6263_);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 1, v_snd_6273_);
                    v___x_6278_ = v_reuseFailAlloc_6285_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6276_ == 0 {
                    lean_ctor_set(v___x_6275_, 1, v___x_6278_);
                    v___x_6280_ = v___x_6275_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6284_, 0, v_fst_6272_);
                    lean_ctor_set(v_reuseFailAlloc_6284_, 1, v___x_6278_);
                    v___x_6280_ = v_reuseFailAlloc_6284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6271_ == 0 {
                    lean_ctor_set(v___x_6270_, 0, v___x_6280_);
                    v___x_6282_ = v___x_6270_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6283_, 0, v___x_6280_);
                    v___x_6282_ = v_reuseFailAlloc_6283_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6282_;
            }
            8 => {
                if v_isShared_6293_ == 0 {
                    v___x_6295_ = v___x_6292_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6296_, 0, v_a_6290_);
                    v___x_6295_ = v_reuseFailAlloc_6296_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd___boxed(
    mut v_n_6298_: *mut LeanObject,
    mut v_mvar_6299_: *mut LeanObject,
    mut v_h_6300_: *mut LeanObject,
    mut v_a_6301_: *mut LeanObject,
    mut v_a_6302_: *mut LeanObject,
    mut v_a_6303_: *mut LeanObject,
    mut v_a_6304_: *mut LeanObject,
    mut v_a_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6306_: *mut LeanObject = core::ptr::null_mut();
    v_res_6306_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
        v_n_6298_,
        v_mvar_6299_,
        v_h_6300_,
        v_a_6301_,
        v_a_6302_,
        v_a_6303_,
        v_a_6304_,
    );
    lean_dec(v_a_6304_);
    lean_dec_ref(v_a_6303_);
    lean_dec(v_a_6302_);
    lean_dec_ref(v_a_6301_);
    lean_dec(v_n_6298_);
    return v_res_6306_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(
    mut v_x_6307_: *mut LeanObject,
    mut v_x_6308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: u8 = 0;
    let mut v_tail_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6321_: u8 = 0;
    let mut v_unused_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6329_: u8 = 0;
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6307_) == 0 {
                    lean_dec(v_x_6308_);
                    v___x_6309_ = lean_box(0);
                    return v___x_6309_;
                } else {
                    v_head_6310_ = lean_ctor_get(v_x_6307_, 0);
                    v___x_6311_ = (lean_unbox(v_head_6310_) as u8);
                    if v___x_6311_ == 0 {
                        v_tail_6312_ = lean_ctor_get(v_x_6307_, 1);
                        v_isSharedCheck_6321_ = (!lean_is_exclusive(v_x_6307_)) as u8;
                        if v_isSharedCheck_6321_ == 0 {
                            v_unused_6322_ = lean_ctor_get(v_x_6307_, 0);
                            lean_dec(v_unused_6322_);
                            v___x_6314_ = v_x_6307_;
                            v_isShared_6315_ = v_isSharedCheck_6321_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_6312_);
                            lean_dec(v_x_6307_);
                            v___x_6314_ = lean_box(0);
                            v_isShared_6315_ = v_isSharedCheck_6321_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_x_6308_) == 0 {
                            lean_dec_ref_known(v_x_6307_, 2);
                            v___x_6323_ = lean_box(0);
                            return v___x_6323_;
                        } else {
                            v_tail_6324_ = lean_ctor_get(v_x_6307_, 1);
                            lean_inc(v_tail_6324_);
                            lean_dec_ref_known(v_x_6307_, 2);
                            v_head_6325_ = lean_ctor_get(v_x_6308_, 0);
                            v_tail_6326_ = lean_ctor_get(v_x_6308_, 1);
                            v_isSharedCheck_6335_ = (!lean_is_exclusive(v_x_6308_)) as u8;
                            if v_isSharedCheck_6335_ == 0 {
                                v___x_6328_ = v_x_6308_;
                                v_isShared_6329_ = v_isSharedCheck_6335_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_tail_6326_);
                                lean_inc(v_head_6325_);
                                lean_dec(v_x_6308_);
                                v___x_6328_ = lean_box(0);
                                v_isShared_6329_ = v_isSharedCheck_6335_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6316_ = lean_box(0);
                v___x_6317_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(
                        v_tail_6312_,
                        v_x_6308_,
                    );
                if v_isShared_6315_ == 0 {
                    lean_ctor_set(v___x_6314_, 1, v___x_6317_);
                    lean_ctor_set(v___x_6314_, 0, v___x_6316_);
                    v___x_6319_ = v___x_6314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6320_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6320_, 0, v___x_6316_);
                    lean_ctor_set(v_reuseFailAlloc_6320_, 1, v___x_6317_);
                    v___x_6319_ = v_reuseFailAlloc_6320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6319_;
            }
            3 => {
                v___x_6330_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6330_, 0, v_head_6325_);
                v___x_6331_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(
                        v_tail_6324_,
                        v_tail_6326_,
                    );
                if v_isShared_6329_ == 0 {
                    lean_ctor_set(v___x_6328_, 1, v___x_6331_);
                    lean_ctor_set(v___x_6328_, 0, v___x_6330_);
                    v___x_6333_ = v___x_6328_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6334_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6334_, 0, v___x_6330_);
                    lean_ctor_set(v_reuseFailAlloc_6334_, 1, v___x_6331_);
                    v___x_6333_ = v_reuseFailAlloc_6334_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge(
    mut v_00_u03b1_6336_: *mut LeanObject,
    mut v_x_6337_: *mut LeanObject,
    mut v_x_6338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    v___x_6339_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(
        v_x_6337_, v_x_6338_,
    );
    return v___x_6339_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(
    mut v_a_6340_: *mut LeanObject,
    mut v_a_6341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6340_) == 0 {
                    v___x_6342_ = l_List_reverse___redArg(v_a_6341_);
                    return v___x_6342_;
                } else {
                    v_head_6343_ = lean_ctor_get(v_a_6340_, 0);
                    v_tail_6344_ = lean_ctor_get(v_a_6340_, 1);
                    v_isSharedCheck_6353_ = (!lean_is_exclusive(v_a_6340_)) as u8;
                    if v_isSharedCheck_6353_ == 0 {
                        v___x_6346_ = v_a_6340_;
                        v_isShared_6347_ = v_isSharedCheck_6353_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6344_);
                        lean_inc(v_head_6343_);
                        lean_dec(v_a_6340_);
                        v___x_6346_ = lean_box(0);
                        v_isShared_6347_ = v_isSharedCheck_6353_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6348_ = l_Lean_mkLevelParam(v_head_6343_);
                if v_isShared_6347_ == 0 {
                    lean_ctor_set(v___x_6346_, 1, v_a_6341_);
                    lean_ctor_set(v___x_6346_, 0, v___x_6348_);
                    v___x_6350_ = v___x_6346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6352_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6352_, 0, v___x_6348_);
                    lean_ctor_set(v_reuseFailAlloc_6352_, 1, v_a_6341_);
                    v___x_6350_ = v_reuseFailAlloc_6352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6340_ = v_tail_6344_;
                v_a_6341_ = v___x_6350_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(
    mut v_constName_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
    mut v___y_6356_: *mut LeanObject,
    mut v___y_6357_: *mut LeanObject,
    mut v___y_6358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: u8 = 0;
    let mut v___x_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6368_: u8 = 0;
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6360_ = lean_st_ref_get(v___y_6358_);
                v_env_6361_ = lean_ctor_get(v___x_6360_, 0);
                lean_inc_ref(v_env_6361_);
                lean_dec(v___x_6360_);
                v___x_6362_ = 0;
                lean_inc(v_constName_6354_);
                v___x_6363_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6361_,
                    v_constName_6354_,
                    v___x_6362_,
                );
                if lean_obj_tag(v___x_6363_) == 0 {
                    v___x_6364_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0_spec__0___redArg(v_constName_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_);
                    return v___x_6364_;
                } else {
                    lean_dec(v_constName_6354_);
                    v_val_6365_ = lean_ctor_get(v___x_6363_, 0);
                    v_isSharedCheck_6372_ = (!lean_is_exclusive(v___x_6363_)) as u8;
                    if v_isSharedCheck_6372_ == 0 {
                        v___x_6367_ = v___x_6363_;
                        v_isShared_6368_ = v_isSharedCheck_6372_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_6365_);
                        lean_dec(v___x_6363_);
                        v___x_6367_ = lean_box(0);
                        v_isShared_6368_ = v_isSharedCheck_6372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6368_ == 0 {
                    lean_ctor_set_tag(v___x_6367_, 0);
                    v___x_6370_ = v___x_6367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_val_6365_);
                    v___x_6370_ = v_reuseFailAlloc_6371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2___boxed(
    mut v_constName_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
    mut v___y_6375_: *mut LeanObject,
    mut v___y_6376_: *mut LeanObject,
    mut v___y_6377_: *mut LeanObject,
    mut v___y_6378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6379_: *mut LeanObject = core::ptr::null_mut();
    v_res_6379_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_6373_, v___y_6374_, v___y_6375_, v___y_6376_, v___y_6377_);
    lean_dec(v___y_6377_);
    lean_dec_ref(v___y_6376_);
    lean_dec(v___y_6375_);
    lean_dec_ref(v___y_6374_);
    return v_res_6379_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(
    mut v_constName_6380_: *mut LeanObject,
    mut v___y_6381_: *mut LeanObject,
    mut v___y_6382_: *mut LeanObject,
    mut v___y_6383_: *mut LeanObject,
    mut v___y_6384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6390_: u8 = 0;
    let mut v_levelParams_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v_a_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6402_: u8 = 0;
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_6380_);
                v___x_6386_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__2(v_constName_6380_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_);
                if lean_obj_tag(v___x_6386_) == 0 {
                    v_a_6387_ = lean_ctor_get(v___x_6386_, 0);
                    v_isSharedCheck_6398_ = (!lean_is_exclusive(v___x_6386_)) as u8;
                    if v_isSharedCheck_6398_ == 0 {
                        v___x_6389_ = v___x_6386_;
                        v_isShared_6390_ = v_isSharedCheck_6398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6387_);
                        lean_dec(v___x_6386_);
                        v___x_6389_ = lean_box(0);
                        v_isShared_6390_ = v_isSharedCheck_6398_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_6380_);
                    v_a_6399_ = lean_ctor_get(v___x_6386_, 0);
                    v_isSharedCheck_6406_ = (!lean_is_exclusive(v___x_6386_)) as u8;
                    if v_isSharedCheck_6406_ == 0 {
                        v___x_6401_ = v___x_6386_;
                        v_isShared_6402_ = v_isSharedCheck_6406_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6399_);
                        lean_dec(v___x_6386_);
                        v___x_6401_ = lean_box(0);
                        v_isShared_6402_ = v_isSharedCheck_6406_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_6391_ = lean_ctor_get(v_a_6387_, 1);
                lean_inc(v_levelParams_6391_);
                lean_dec(v_a_6387_);
                v___x_6392_ = lean_box(0);
                v___x_6393_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_6391_, v___x_6392_);
                v___x_6394_ = l_Lean_mkConst(v_constName_6380_, v___x_6393_);
                if v_isShared_6390_ == 0 {
                    lean_ctor_set(v___x_6389_, 0, v___x_6394_);
                    v___x_6396_ = v___x_6389_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6397_, 0, v___x_6394_);
                    v___x_6396_ = v_reuseFailAlloc_6397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6396_;
            }
            3 => {
                if v_isShared_6402_ == 0 {
                    v___x_6404_ = v___x_6401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_a_6399_);
                    v___x_6404_ = v_reuseFailAlloc_6405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2___boxed(
    mut v_constName_6407_: *mut LeanObject,
    mut v___y_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6413_: *mut LeanObject = core::ptr::null_mut();
    v_res_6413_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_constName_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_);
    lean_dec(v___y_6411_);
    lean_dec_ref(v___y_6410_);
    lean_dec(v___y_6409_);
    lean_dec_ref(v___y_6408_);
    return v_res_6413_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(
    mut v_x_6414_: *mut LeanObject,
    mut v_x_6415_: *mut LeanObject,
    mut v___y_6416_: *mut LeanObject,
    mut v___y_6417_: *mut LeanObject,
    mut v___y_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6427_: u8 = 0;
    let mut v_a_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: u8 = 0;
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6442_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6446_: u8 = 0;
    let mut v_val_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6449_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6414_) == 0 {
                    v___x_6421_ = l_List_reverse___redArg(v_x_6415_);
                    v___x_6422_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6422_, 0, v___x_6421_);
                    return v___x_6422_;
                } else {
                    v_head_6423_ = lean_ctor_get(v_x_6414_, 0);
                    v_tail_6424_ = lean_ctor_get(v_x_6414_, 1);
                    v_isSharedCheck_6449_ = (!lean_is_exclusive(v_x_6414_)) as u8;
                    if v_isSharedCheck_6449_ == 0 {
                        v___x_6426_ = v_x_6414_;
                        v_isShared_6427_ = v_isSharedCheck_6449_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6424_);
                        lean_inc(v_head_6423_);
                        lean_dec(v_x_6414_);
                        v___x_6426_ = lean_box(0);
                        v_isShared_6427_ = v_isSharedCheck_6449_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_head_6423_) == 0 {
                    v___x_6434_ = lean_box(0);
                    v___x_6435_ = 0;
                    v___x_6436_ = lean_box(0);
                    v___x_6437_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_6434_,
                        v___x_6435_,
                        v___x_6436_,
                        v___y_6416_,
                        v___y_6417_,
                        v___y_6418_,
                        v___y_6419_,
                    );
                    if lean_obj_tag(v___x_6437_) == 0 {
                        v_a_6438_ = lean_ctor_get(v___x_6437_, 0);
                        lean_inc(v_a_6438_);
                        lean_dec_ref_known(v___x_6437_, 1);
                        v_a_6429_ = v_a_6438_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_6426_);
                        lean_dec(v_tail_6424_);
                        lean_dec(v_x_6415_);
                        v_a_6439_ = lean_ctor_get(v___x_6437_, 0);
                        v_isSharedCheck_6446_ = (!lean_is_exclusive(v___x_6437_)) as u8;
                        if v_isSharedCheck_6446_ == 0 {
                            v___x_6441_ = v___x_6437_;
                            v_isShared_6442_ = v_isSharedCheck_6446_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6439_);
                            lean_dec(v___x_6437_);
                            v___x_6441_ = lean_box(0);
                            v_isShared_6442_ = v_isSharedCheck_6446_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_val_6447_ = lean_ctor_get(v_head_6423_, 0);
                    lean_inc(v_val_6447_);
                    lean_dec_ref_known(v_head_6423_, 1);
                    v___x_6448_ = l_Lean_mkFVar(v_val_6447_);
                    v_a_6429_ = v___x_6448_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6427_ == 0 {
                    lean_ctor_set(v___x_6426_, 1, v_x_6415_);
                    lean_ctor_set(v___x_6426_, 0, v_a_6429_);
                    v___x_6431_ = v___x_6426_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6433_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6433_, 0, v_a_6429_);
                    lean_ctor_set(v_reuseFailAlloc_6433_, 1, v_x_6415_);
                    v___x_6431_ = v_reuseFailAlloc_6433_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_6414_ = v_tail_6424_;
                v_x_6415_ = v___x_6431_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_6442_ == 0 {
                    v___x_6444_ = v___x_6441_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
                    v___x_6444_ = v_reuseFailAlloc_6445_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1___boxed(
    mut v_x_6450_: *mut LeanObject,
    mut v_x_6451_: *mut LeanObject,
    mut v___y_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6457_: *mut LeanObject = core::ptr::null_mut();
    v_res_6457_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v_x_6450_, v_x_6451_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_);
    lean_dec(v___y_6455_);
    lean_dec_ref(v___y_6454_);
    lean_dec(v___y_6453_);
    lean_dec_ref(v___y_6452_);
    return v_res_6457_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(
    mut v_a_6458_: *mut LeanObject,
    mut v_a_6459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6465_: u8 = 0;
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6458_) == 0 {
                    v___x_6460_ = l_List_reverse___redArg(v_a_6459_);
                    return v___x_6460_;
                } else {
                    v_head_6461_ = lean_ctor_get(v_a_6458_, 0);
                    v_tail_6462_ = lean_ctor_get(v_a_6458_, 1);
                    v_isSharedCheck_6471_ = (!lean_is_exclusive(v_a_6458_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v___x_6464_ = v_a_6458_;
                        v_isShared_6465_ = v_isSharedCheck_6471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6462_);
                        lean_inc(v_head_6461_);
                        lean_dec(v_a_6458_);
                        v___x_6464_ = lean_box(0);
                        v_isShared_6465_ = v_isSharedCheck_6471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6466_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6466_, 0, v_head_6461_);
                if v_isShared_6465_ == 0 {
                    lean_ctor_set(v___x_6464_, 1, v_a_6459_);
                    lean_ctor_set(v___x_6464_, 0, v___x_6466_);
                    v___x_6468_ = v___x_6464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6470_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6470_, 0, v___x_6466_);
                    lean_ctor_set(v_reuseFailAlloc_6470_, 1, v_a_6459_);
                    v___x_6468_ = v_reuseFailAlloc_6470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6458_ = v_tail_6462_;
                v_a_6459_ = v___x_6468_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(
    mut v_gs_6474_: *mut LeanObject,
    mut v_variablesKept_6475_: *mut LeanObject,
    mut v_snd_6476_: *mut LeanObject,
    mut v_fst_6477_: *mut LeanObject,
    mut v_fst_6478_: *mut LeanObject,
    mut v___y_6479_: *mut LeanObject,
    mut v___y_6480_: *mut LeanObject,
    mut v___y_6481_: *mut LeanObject,
    mut v___y_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6509_: u8 = 0;
    let mut v___x_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6513_: u8 = 0;
    let mut v_a_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6521_: u8 = 0;
    let mut v_a_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6525_: u8 = 0;
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6529_: u8 = 0;
    let mut v_a_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6533_: u8 = 0;
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6537_: u8 = 0;
    let mut v_a_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6541_: u8 = 0;
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_6484_ = lean_ctor_get(v___y_6479_, 2);
                v___x_6485_ = l_Lean_LocalContext_getFVarIds(v_lctx_6484_);
                v___x_6486_ = lean_array_to_list(v___x_6485_);
                v___x_6487_ = l_List_lengthTR___redArg(v_gs_6474_);
                v___x_6488_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0;
                lean_inc(v___x_6486_);
                v___x_6489_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    lean_box(0),
                    v___x_6486_,
                    v___x_6486_,
                    v___x_6487_,
                    v___x_6488_,
                );
                lean_dec(v___x_6486_);
                v___x_6490_ = lean_box(0);
                v___x_6491_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__0(v___x_6489_, v___x_6490_);
                v___x_6492_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_listBoolMerge___redArg(
                        v_variablesKept_6475_,
                        v_snd_6476_,
                    );
                v___x_6493_ = l_List_appendTR___redArg(v___x_6491_, v___x_6492_);
                v___x_6494_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__1(v___x_6493_, v___x_6490_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                if lean_obj_tag(v___x_6494_) == 0 {
                    v_a_6495_ = lean_ctor_get(v___x_6494_, 0);
                    lean_inc(v_a_6495_);
                    lean_dec_ref_known(v___x_6494_, 1);
                    v___x_6496_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2(v_fst_6477_, v___y_6479_, v___y_6480_, v___y_6481_, v___y_6482_);
                    if lean_obj_tag(v___x_6496_) == 0 {
                        v_a_6497_ = lean_ctor_get(v___x_6496_, 0);
                        lean_inc(v_a_6497_);
                        lean_dec_ref_known(v___x_6496_, 1);
                        v___x_6498_ = lean_array_mk(v_a_6495_);
                        v___x_6499_ = l_Lean_mkAppN(v_a_6497_, v___x_6498_);
                        lean_dec_ref(v___x_6498_);
                        lean_inc(v___y_6482_);
                        lean_inc_ref(v___y_6481_);
                        lean_inc(v___y_6480_);
                        lean_inc_ref(v___y_6479_);
                        lean_inc_ref(v___x_6499_);
                        v___x_6500_ = lean_infer_type(
                            v___x_6499_,
                            v___y_6479_,
                            v___y_6480_,
                            v___y_6481_,
                            v___y_6482_,
                        );
                        if lean_obj_tag(v___x_6500_) == 0 {
                            v_a_6501_ = lean_ctor_get(v___x_6500_, 0);
                            lean_inc(v_a_6501_);
                            lean_dec_ref_known(v___x_6500_, 1);
                            lean_inc(v_fst_6478_);
                            v___x_6502_ = l_Lean_MVarId_getType(
                                v_fst_6478_,
                                v___y_6479_,
                                v___y_6480_,
                                v___y_6481_,
                                v___y_6482_,
                            );
                            if lean_obj_tag(v___x_6502_) == 0 {
                                v_a_6503_ = lean_ctor_get(v___x_6502_, 0);
                                lean_inc(v_a_6503_);
                                lean_dec_ref_known(v___x_6502_, 1);
                                v___x_6504_ = l_Lean_Meta_isExprDefEq(
                                    v_a_6501_,
                                    v_a_6503_,
                                    v___y_6479_,
                                    v___y_6480_,
                                    v___y_6481_,
                                    v___y_6482_,
                                );
                                lean_dec(v___y_6482_);
                                lean_dec_ref(v___y_6481_);
                                lean_dec_ref(v___y_6479_);
                                if lean_obj_tag(v___x_6504_) == 0 {
                                    lean_dec_ref_known(v___x_6504_, 1);
                                    v___x_6505_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__1___redArg(v_fst_6478_, v___x_6499_, v___y_6480_);
                                    lean_dec(v___y_6480_);
                                    return v___x_6505_;
                                } else {
                                    lean_dec_ref(v___x_6499_);
                                    lean_dec(v___y_6480_);
                                    lean_dec(v_fst_6478_);
                                    v_a_6506_ = lean_ctor_get(v___x_6504_, 0);
                                    v_isSharedCheck_6513_ = (!lean_is_exclusive(v___x_6504_)) as u8;
                                    if v_isSharedCheck_6513_ == 0 {
                                        v___x_6508_ = v___x_6504_;
                                        v_isShared_6509_ = v_isSharedCheck_6513_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6506_);
                                        lean_dec(v___x_6504_);
                                        v___x_6508_ = lean_box(0);
                                        v_isShared_6509_ = v_isSharedCheck_6513_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6501_);
                                lean_dec_ref(v___x_6499_);
                                lean_dec(v___y_6482_);
                                lean_dec_ref(v___y_6481_);
                                lean_dec(v___y_6480_);
                                lean_dec_ref(v___y_6479_);
                                lean_dec(v_fst_6478_);
                                v_a_6514_ = lean_ctor_get(v___x_6502_, 0);
                                v_isSharedCheck_6521_ = (!lean_is_exclusive(v___x_6502_)) as u8;
                                if v_isSharedCheck_6521_ == 0 {
                                    v___x_6516_ = v___x_6502_;
                                    v_isShared_6517_ = v_isSharedCheck_6521_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6514_);
                                    lean_dec(v___x_6502_);
                                    v___x_6516_ = lean_box(0);
                                    v_isShared_6517_ = v_isSharedCheck_6521_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_6499_);
                            lean_dec(v___y_6482_);
                            lean_dec_ref(v___y_6481_);
                            lean_dec(v___y_6480_);
                            lean_dec_ref(v___y_6479_);
                            lean_dec(v_fst_6478_);
                            v_a_6522_ = lean_ctor_get(v___x_6500_, 0);
                            v_isSharedCheck_6529_ = (!lean_is_exclusive(v___x_6500_)) as u8;
                            if v_isSharedCheck_6529_ == 0 {
                                v___x_6524_ = v___x_6500_;
                                v_isShared_6525_ = v_isSharedCheck_6529_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6522_);
                                lean_dec(v___x_6500_);
                                v___x_6524_ = lean_box(0);
                                v_isShared_6525_ = v_isSharedCheck_6529_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6495_);
                        lean_dec(v___y_6482_);
                        lean_dec_ref(v___y_6481_);
                        lean_dec(v___y_6480_);
                        lean_dec_ref(v___y_6479_);
                        lean_dec(v_fst_6478_);
                        v_a_6530_ = lean_ctor_get(v___x_6496_, 0);
                        v_isSharedCheck_6537_ = (!lean_is_exclusive(v___x_6496_)) as u8;
                        if v_isSharedCheck_6537_ == 0 {
                            v___x_6532_ = v___x_6496_;
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6530_);
                            lean_dec(v___x_6496_);
                            v___x_6532_ = lean_box(0);
                            v_isShared_6533_ = v_isSharedCheck_6537_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_6482_);
                    lean_dec_ref(v___y_6481_);
                    lean_dec(v___y_6480_);
                    lean_dec_ref(v___y_6479_);
                    lean_dec(v_fst_6478_);
                    lean_dec(v_fst_6477_);
                    v_a_6538_ = lean_ctor_get(v___x_6494_, 0);
                    v_isSharedCheck_6545_ = (!lean_is_exclusive(v___x_6494_)) as u8;
                    if v_isSharedCheck_6545_ == 0 {
                        v___x_6540_ = v___x_6494_;
                        v_isShared_6541_ = v_isSharedCheck_6545_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6538_);
                        lean_dec(v___x_6494_);
                        v___x_6540_ = lean_box(0);
                        v_isShared_6541_ = v_isSharedCheck_6545_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6509_ == 0 {
                    v___x_6511_ = v___x_6508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6512_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6512_, 0, v_a_6506_);
                    v___x_6511_ = v_reuseFailAlloc_6512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6511_;
            }
            3 => {
                if v_isShared_6517_ == 0 {
                    v___x_6519_ = v___x_6516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6520_, 0, v_a_6514_);
                    v___x_6519_ = v_reuseFailAlloc_6520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6519_;
            }
            5 => {
                if v_isShared_6525_ == 0 {
                    v___x_6527_ = v___x_6524_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6528_, 0, v_a_6522_);
                    v___x_6527_ = v_reuseFailAlloc_6528_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6527_;
            }
            7 => {
                if v_isShared_6533_ == 0 {
                    v___x_6535_ = v___x_6532_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_a_6530_);
                    v___x_6535_ = v_reuseFailAlloc_6536_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6535_;
            }
            9 => {
                if v_isShared_6541_ == 0 {
                    v___x_6543_ = v___x_6540_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6544_, 0, v_a_6538_);
                    v___x_6543_ = v_reuseFailAlloc_6544_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed(
    mut v_gs_6546_: *mut LeanObject,
    mut v_variablesKept_6547_: *mut LeanObject,
    mut v_snd_6548_: *mut LeanObject,
    mut v_fst_6549_: *mut LeanObject,
    mut v_fst_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6556_: *mut LeanObject = core::ptr::null_mut();
    v_res_6556_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0(v_gs_6546_, v_variablesKept_6547_, v_snd_6548_, v_fst_6549_, v_fst_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_);
    lean_dec(v_gs_6546_);
    return v_res_6556_;
}
pub unsafe fn _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__0;
    v___x_6559_ = l_Lean_stringToMessageData(v___x_6558_);
    return v___x_6559_;
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(
    mut v_x_6560_: *mut LeanObject,
    mut v_x_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
    mut v___y_6565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: u8 = 0;
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toInductionSubgoal_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6591_: u8 = 0;
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6595_: u8 = 0;
    let mut v_a_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6561_) == 0 {
                    v___x_6567_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6567_, 0, v_x_6560_);
                    return v___x_6567_;
                } else {
                    v_tail_6568_ = lean_ctor_get(v_x_6561_, 1);
                    v___x_6569_ = 0;
                    v___x_6570_ = l_Lean_Meta_intro1Core(
                        v_x_6560_,
                        v___x_6569_,
                        v___y_6562_,
                        v___y_6563_,
                        v___y_6564_,
                        v___y_6565_,
                    );
                    if lean_obj_tag(v___x_6570_) == 0 {
                        v_a_6571_ = lean_ctor_get(v___x_6570_, 0);
                        lean_inc(v_a_6571_);
                        lean_dec_ref_known(v___x_6570_, 1);
                        v_fst_6572_ = lean_ctor_get(v_a_6571_, 0);
                        lean_inc(v_fst_6572_);
                        v_snd_6573_ = lean_ctor_get(v_a_6571_, 1);
                        lean_inc(v_snd_6573_);
                        lean_dec(v_a_6571_);
                        v___x_6574_ = lean_unsigned_to_nat(0);
                        v___x_6575_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0;
                        v___x_6576_ = lean_box(0);
                        v___x_6577_ = l_Lean_MVarId_cases(
                            v_snd_6573_,
                            v_fst_6572_,
                            v___x_6575_,
                            v___x_6569_,
                            v___x_6576_,
                            v___y_6562_,
                            v___y_6563_,
                            v___y_6564_,
                            v___y_6565_,
                        );
                        if lean_obj_tag(v___x_6577_) == 0 {
                            v_a_6578_ = lean_ctor_get(v___x_6577_, 0);
                            lean_inc(v_a_6578_);
                            lean_dec_ref_known(v___x_6577_, 1);
                            v___x_6579_ = lean_array_get_size(v_a_6578_);
                            v___x_6580_ = lean_unsigned_to_nat(1);
                            v___x_6581_ = lean_nat_dec_eq(v___x_6579_, v___x_6580_);
                            if v___x_6581_ == 0 {
                                lean_dec(v_a_6578_);
                                v___x_6582_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1), core::ptr::addr_of_mut!(l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1_once), _init_l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___closed__1);
                                v___x_6583_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_6582_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_);
                                return v___x_6583_;
                            } else {
                                v___x_6584_ = lean_array_fget(v_a_6578_, v___x_6574_);
                                lean_dec(v_a_6578_);
                                v_toInductionSubgoal_6585_ = lean_ctor_get(v___x_6584_, 0);
                                lean_inc_ref(v_toInductionSubgoal_6585_);
                                lean_dec(v___x_6584_);
                                v_mvarId_6586_ = lean_ctor_get(v_toInductionSubgoal_6585_, 0);
                                lean_inc(v_mvarId_6586_);
                                lean_dec_ref(v_toInductionSubgoal_6585_);
                                v_x_6560_ = v_mvarId_6586_;
                                v_x_6561_ = v_tail_6568_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v_a_6588_ = lean_ctor_get(v___x_6577_, 0);
                            v_isSharedCheck_6595_ = (!lean_is_exclusive(v___x_6577_)) as u8;
                            if v_isSharedCheck_6595_ == 0 {
                                v___x_6590_ = v___x_6577_;
                                v_isShared_6591_ = v_isSharedCheck_6595_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6588_);
                                lean_dec(v___x_6577_);
                                v___x_6590_ = lean_box(0);
                                v_isShared_6591_ = v_isSharedCheck_6595_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_6596_ = lean_ctor_get(v___x_6570_, 0);
                        v_isSharedCheck_6603_ = (!lean_is_exclusive(v___x_6570_)) as u8;
                        if v_isSharedCheck_6603_ == 0 {
                            v___x_6598_ = v___x_6570_;
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6596_);
                            lean_dec(v___x_6570_);
                            v___x_6598_ = lean_box(0);
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6591_ == 0 {
                    v___x_6593_ = v___x_6590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6594_, 0, v_a_6588_);
                    v___x_6593_ = v_reuseFailAlloc_6594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6593_;
            }
            3 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4___boxed(
    mut v_x_6604_: *mut LeanObject,
    mut v_x_6605_: *mut LeanObject,
    mut v___y_6606_: *mut LeanObject,
    mut v___y_6607_: *mut LeanObject,
    mut v___y_6608_: *mut LeanObject,
    mut v___y_6609_: *mut LeanObject,
    mut v___y_6610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6611_: *mut LeanObject = core::ptr::null_mut();
    v_res_6611_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_x_6604_, v_x_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_);
    lean_dec(v___y_6609_);
    lean_dec_ref(v___y_6608_);
    lean_dec(v___y_6607_);
    lean_dec_ref(v___y_6606_);
    lean_dec(v_x_6605_);
    return v_res_6611_;
}
pub unsafe fn l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(
    mut v_a_6612_: *mut LeanObject,
    mut v_a_6613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: u8 = 0;
    let mut v_tail_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6622_: u8 = 0;
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6627_: u8 = 0;
    let mut v_unused_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6612_) == 0 {
                    v___x_6614_ = l_List_reverse___redArg(v_a_6613_);
                    return v___x_6614_;
                } else {
                    v_head_6615_ = lean_ctor_get(v_a_6612_, 0);
                    v___x_6616_ = (lean_unbox(v_head_6615_) as u8);
                    if v___x_6616_ == 0 {
                        v_tail_6617_ = lean_ctor_get(v_a_6612_, 1);
                        lean_inc(v_tail_6617_);
                        lean_dec_ref_known(v_a_6612_, 2);
                        v_a_6612_ = v_tail_6617_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_head_6615_);
                        v_tail_6619_ = lean_ctor_get(v_a_6612_, 1);
                        v_isSharedCheck_6627_ = (!lean_is_exclusive(v_a_6612_)) as u8;
                        if v_isSharedCheck_6627_ == 0 {
                            v_unused_6628_ = lean_ctor_get(v_a_6612_, 0);
                            lean_dec(v_unused_6628_);
                            v___x_6621_ = v_a_6612_;
                            v_isShared_6622_ = v_isSharedCheck_6627_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_6619_);
                            lean_dec(v_a_6612_);
                            v___x_6621_ = lean_box(0);
                            v_isShared_6622_ = v_isSharedCheck_6627_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_6622_ == 0 {
                    lean_ctor_set(v___x_6621_, 1, v_a_6613_);
                    v___x_6624_ = v___x_6621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6626_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6626_, 0, v_head_6615_);
                    lean_ctor_set(v_reuseFailAlloc_6626_, 1, v_a_6613_);
                    v___x_6624_ = v_reuseFailAlloc_6626_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6612_ = v_tail_6619_;
                v_a_6613_ = v___x_6624_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(
    mut v_gs_6629_: *mut LeanObject,
    mut v_x_6630_: *mut LeanObject,
    mut v_x_6631_: *mut LeanObject,
    mut v___y_6632_: *mut LeanObject,
    mut v___y_6633_: *mut LeanObject,
    mut v___y_6634_: *mut LeanObject,
    mut v___y_6635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6646_: u8 = 0;
    let mut v_fst_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_variablesKept_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neqs_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6669_: u8 = 0;
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6673_: u8 = 0;
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6690_: u8 = 0;
    let mut v_val_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6694_: u8 = 0;
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6705_: u8 = 0;
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6709_: u8 = 0;
    let mut v_a_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6713_: u8 = 0;
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_6722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6738_: u8 = 0;
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6742_: u8 = 0;
    let mut v_a_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6750_: u8 = 0;
    let mut v_a_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6754_: u8 = 0;
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6758_: u8 = 0;
    let mut v_a_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6762_: u8 = 0;
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6766_: u8 = 0;
    let mut v_isSharedCheck_6767_: u8 = 0;
    let mut v_unused_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6630_) == 0 {
                    lean_dec(v_gs_6629_);
                    v___x_6637_ = l_List_reverse___redArg(v_x_6631_);
                    v___x_6638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6638_, 0, v___x_6637_);
                    return v___x_6638_;
                } else {
                    v_head_6639_ = lean_ctor_get(v_x_6630_, 0);
                    lean_inc(v_head_6639_);
                    v_snd_6640_ = lean_ctor_get(v_head_6639_, 1);
                    v_fst_6641_ = lean_ctor_get(v_snd_6640_, 0);
                    lean_inc(v_fst_6641_);
                    v_snd_6642_ = lean_ctor_get(v_snd_6640_, 1);
                    lean_inc(v_snd_6642_);
                    v_tail_6643_ = lean_ctor_get(v_x_6630_, 1);
                    v_isSharedCheck_6767_ = (!lean_is_exclusive(v_x_6630_)) as u8;
                    if v_isSharedCheck_6767_ == 0 {
                        v_unused_6768_ = lean_ctor_get(v_x_6630_, 0);
                        lean_dec(v_unused_6768_);
                        v___x_6645_ = v_x_6630_;
                        v_isShared_6646_ = v_isSharedCheck_6767_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6643_);
                        lean_dec(v_x_6630_);
                        v___x_6645_ = lean_box(0);
                        v_isShared_6646_ = v_isSharedCheck_6767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6647_ = lean_ctor_get(v_head_6639_, 0);
                lean_inc(v_fst_6647_);
                lean_dec(v_head_6639_);
                v_fst_6648_ = lean_ctor_get(v_fst_6641_, 0);
                lean_inc(v_fst_6648_);
                v_snd_6649_ = lean_ctor_get(v_fst_6641_, 1);
                lean_inc(v_snd_6649_);
                lean_dec(v_fst_6641_);
                v_variablesKept_6650_ = lean_ctor_get(v_snd_6642_, 0);
                lean_inc_n(v_variablesKept_6650_, 2);
                v_neqs_6651_ = lean_ctor_get(v_snd_6642_, 1);
                lean_inc(v_neqs_6651_);
                lean_dec(v_snd_6642_);
                v___x_6674_ = lean_box(0);
                v___x_6675_ = l_List_filterTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__3(v_variablesKept_6650_, v___x_6674_);
                v___x_6676_ = l_List_lengthTR___redArg(v___x_6675_);
                lean_dec(v___x_6675_);
                if lean_obj_tag(v_neqs_6651_) == 0 {
                    v___x_6677_ = lean_unsigned_to_nat(1);
                    v___x_6678_ = lean_nat_sub(v___x_6676_, v___x_6677_);
                    lean_dec(v___x_6676_);
                    v___x_6679_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
                            v___x_6678_,
                            v_snd_6649_,
                            v_fst_6648_,
                            v___y_6632_,
                            v___y_6633_,
                            v___y_6634_,
                            v___y_6635_,
                        );
                    lean_dec(v___x_6678_);
                    if lean_obj_tag(v___x_6679_) == 0 {
                        v_a_6680_ = lean_ctor_get(v___x_6679_, 0);
                        lean_inc(v_a_6680_);
                        lean_dec_ref_known(v___x_6679_, 1);
                        v_fst_6681_ = lean_ctor_get(v_a_6680_, 0);
                        lean_inc(v_fst_6681_);
                        v_snd_6682_ = lean_ctor_get(v_a_6680_, 1);
                        lean_inc(v_snd_6682_);
                        lean_dec(v_a_6680_);
                        v_fst_6653_ = v_fst_6681_;
                        v_snd_6654_ = v_snd_6682_;
                        v___y_6655_ = v___y_6632_;
                        v___y_6656_ = v___y_6633_;
                        v___y_6657_ = v___y_6634_;
                        v___y_6658_ = v___y_6635_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_variablesKept_6650_);
                        lean_dec(v_fst_6647_);
                        lean_del_object(v___x_6645_);
                        lean_dec(v_tail_6643_);
                        lean_dec(v_x_6631_);
                        lean_dec(v_gs_6629_);
                        v_a_6683_ = lean_ctor_get(v___x_6679_, 0);
                        v_isSharedCheck_6690_ = (!lean_is_exclusive(v___x_6679_)) as u8;
                        if v_isSharedCheck_6690_ == 0 {
                            v___x_6685_ = v___x_6679_;
                            v_isShared_6686_ = v_isSharedCheck_6690_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6683_);
                            lean_dec(v___x_6679_);
                            v___x_6685_ = lean_box(0);
                            v_isShared_6686_ = v_isSharedCheck_6690_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_val_6691_ = lean_ctor_get(v_neqs_6651_, 0);
                    lean_inc(v_val_6691_);
                    lean_dec_ref_known(v_neqs_6651_, 1);
                    v___x_6692_ = lean_box(0);
                    v_zero_6693_ = lean_unsigned_to_nat(0);
                    v_isZero_6694_ = lean_nat_dec_eq(v_val_6691_, v_zero_6693_);
                    if v_isZero_6694_ == 1 {
                        lean_dec(v_val_6691_);
                        v___x_6695_ =
                            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
                                v___x_6676_,
                                v_snd_6649_,
                                v_fst_6648_,
                                v___y_6632_,
                                v___y_6633_,
                                v___y_6634_,
                                v___y_6635_,
                            );
                        lean_dec(v___x_6676_);
                        if lean_obj_tag(v___x_6695_) == 0 {
                            v_a_6696_ = lean_ctor_get(v___x_6695_, 0);
                            lean_inc(v_a_6696_);
                            lean_dec_ref_known(v___x_6695_, 1);
                            v_fst_6697_ = lean_ctor_get(v_a_6696_, 0);
                            lean_inc(v_fst_6697_);
                            v_snd_6698_ = lean_ctor_get(v_a_6696_, 1);
                            lean_inc(v_snd_6698_);
                            lean_dec(v_a_6696_);
                            v___x_6699_ = l_List_getLast_x21___redArg(v___x_6692_, v_snd_6698_);
                            v___x_6700_ = l_Lean_MVarId_tryClear(
                                v_fst_6697_,
                                v___x_6699_,
                                v___y_6632_,
                                v___y_6633_,
                                v___y_6634_,
                                v___y_6635_,
                            );
                            if lean_obj_tag(v___x_6700_) == 0 {
                                v_a_6701_ = lean_ctor_get(v___x_6700_, 0);
                                lean_inc(v_a_6701_);
                                lean_dec_ref_known(v___x_6700_, 1);
                                v_fst_6653_ = v_a_6701_;
                                v_snd_6654_ = v_snd_6698_;
                                v___y_6655_ = v___y_6632_;
                                v___y_6656_ = v___y_6633_;
                                v___y_6657_ = v___y_6634_;
                                v___y_6658_ = v___y_6635_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_snd_6698_);
                                lean_dec(v_variablesKept_6650_);
                                lean_dec(v_fst_6647_);
                                lean_del_object(v___x_6645_);
                                lean_dec(v_tail_6643_);
                                lean_dec(v_x_6631_);
                                lean_dec(v_gs_6629_);
                                v_a_6702_ = lean_ctor_get(v___x_6700_, 0);
                                v_isSharedCheck_6709_ = (!lean_is_exclusive(v___x_6700_)) as u8;
                                if v_isSharedCheck_6709_ == 0 {
                                    v___x_6704_ = v___x_6700_;
                                    v_isShared_6705_ = v_isSharedCheck_6709_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_6702_);
                                    lean_dec(v___x_6700_);
                                    v___x_6704_ = lean_box(0);
                                    v_isShared_6705_ = v_isSharedCheck_6709_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_variablesKept_6650_);
                            lean_dec(v_fst_6647_);
                            lean_del_object(v___x_6645_);
                            lean_dec(v_tail_6643_);
                            lean_dec(v_x_6631_);
                            lean_dec(v_gs_6629_);
                            v_a_6710_ = lean_ctor_get(v___x_6695_, 0);
                            v_isSharedCheck_6717_ = (!lean_is_exclusive(v___x_6695_)) as u8;
                            if v_isSharedCheck_6717_ == 0 {
                                v___x_6712_ = v___x_6695_;
                                v_isShared_6713_ = v_isSharedCheck_6717_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_6710_);
                                lean_dec(v___x_6695_);
                                v___x_6712_ = lean_box(0);
                                v_isShared_6713_ = v_isSharedCheck_6717_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v___x_6718_ =
                            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
                                v___x_6676_,
                                v_snd_6649_,
                                v_fst_6648_,
                                v___y_6632_,
                                v___y_6633_,
                                v___y_6634_,
                                v___y_6635_,
                            );
                        lean_dec(v___x_6676_);
                        if lean_obj_tag(v___x_6718_) == 0 {
                            v_a_6719_ = lean_ctor_get(v___x_6718_, 0);
                            lean_inc(v_a_6719_);
                            lean_dec_ref_known(v___x_6718_, 1);
                            v_fst_6720_ = lean_ctor_get(v_a_6719_, 0);
                            lean_inc(v_fst_6720_);
                            v_snd_6721_ = lean_ctor_get(v_a_6719_, 1);
                            lean_inc(v_snd_6721_);
                            lean_dec(v_a_6719_);
                            v_one_6722_ = lean_unsigned_to_nat(1);
                            v_n_6723_ = lean_nat_sub(v_val_6691_, v_one_6722_);
                            lean_dec(v_val_6691_);
                            v___x_6724_ = l_List_getLast_x21___redArg(v___x_6692_, v_snd_6721_);
                            v___x_6725_ =
                                l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesProd(
                                    v_n_6723_,
                                    v_fst_6720_,
                                    v___x_6724_,
                                    v___y_6632_,
                                    v___y_6633_,
                                    v___y_6634_,
                                    v___y_6635_,
                                );
                            lean_dec(v_n_6723_);
                            if lean_obj_tag(v___x_6725_) == 0 {
                                v_a_6726_ = lean_ctor_get(v___x_6725_, 0);
                                lean_inc(v_a_6726_);
                                lean_dec_ref_known(v___x_6725_, 1);
                                v_fst_6727_ = lean_ctor_get(v_a_6726_, 0);
                                lean_inc(v_fst_6727_);
                                v_snd_6728_ = lean_ctor_get(v_a_6726_, 1);
                                lean_inc_n(v_snd_6728_, 2);
                                lean_dec(v_a_6726_);
                                v___x_6729_ = lean_array_mk(v_snd_6728_);
                                v___x_6730_ = l_Lean_MVarId_revert(
                                    v_fst_6727_,
                                    v___x_6729_,
                                    v_isZero_6694_,
                                    v_isZero_6694_,
                                    v___y_6632_,
                                    v___y_6633_,
                                    v___y_6634_,
                                    v___y_6635_,
                                );
                                if lean_obj_tag(v___x_6730_) == 0 {
                                    v_a_6731_ = lean_ctor_get(v___x_6730_, 0);
                                    lean_inc(v_a_6731_);
                                    lean_dec_ref_known(v___x_6730_, 1);
                                    v_snd_6732_ = lean_ctor_get(v_a_6731_, 1);
                                    lean_inc(v_snd_6732_);
                                    lean_dec(v_a_6731_);
                                    v___x_6733_ = l_List_foldlM___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__4(v_snd_6732_, v_snd_6728_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_);
                                    lean_dec(v_snd_6728_);
                                    if lean_obj_tag(v___x_6733_) == 0 {
                                        v_a_6734_ = lean_ctor_get(v___x_6733_, 0);
                                        lean_inc(v_a_6734_);
                                        lean_dec_ref_known(v___x_6733_, 1);
                                        v_fst_6653_ = v_a_6734_;
                                        v_snd_6654_ = v_snd_6721_;
                                        v___y_6655_ = v___y_6632_;
                                        v___y_6656_ = v___y_6633_;
                                        v___y_6657_ = v___y_6634_;
                                        v___y_6658_ = v___y_6635_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_snd_6721_);
                                        lean_dec(v_variablesKept_6650_);
                                        lean_dec(v_fst_6647_);
                                        lean_del_object(v___x_6645_);
                                        lean_dec(v_tail_6643_);
                                        lean_dec(v_x_6631_);
                                        lean_dec(v_gs_6629_);
                                        v_a_6735_ = lean_ctor_get(v___x_6733_, 0);
                                        v_isSharedCheck_6742_ =
                                            (!lean_is_exclusive(v___x_6733_)) as u8;
                                        if v_isSharedCheck_6742_ == 0 {
                                            v___x_6737_ = v___x_6733_;
                                            v_isShared_6738_ = v_isSharedCheck_6742_;
                                            state = 12;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6735_);
                                            lean_dec(v___x_6733_);
                                            v___x_6737_ = lean_box(0);
                                            v_isShared_6738_ = v_isSharedCheck_6742_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_snd_6728_);
                                    lean_dec(v_snd_6721_);
                                    lean_dec(v_variablesKept_6650_);
                                    lean_dec(v_fst_6647_);
                                    lean_del_object(v___x_6645_);
                                    lean_dec(v_tail_6643_);
                                    lean_dec(v_x_6631_);
                                    lean_dec(v_gs_6629_);
                                    v_a_6743_ = lean_ctor_get(v___x_6730_, 0);
                                    v_isSharedCheck_6750_ = (!lean_is_exclusive(v___x_6730_)) as u8;
                                    if v_isSharedCheck_6750_ == 0 {
                                        v___x_6745_ = v___x_6730_;
                                        v_isShared_6746_ = v_isSharedCheck_6750_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6743_);
                                        lean_dec(v___x_6730_);
                                        v___x_6745_ = lean_box(0);
                                        v_isShared_6746_ = v_isSharedCheck_6750_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_snd_6721_);
                                lean_dec(v_variablesKept_6650_);
                                lean_dec(v_fst_6647_);
                                lean_del_object(v___x_6645_);
                                lean_dec(v_tail_6643_);
                                lean_dec(v_x_6631_);
                                lean_dec(v_gs_6629_);
                                v_a_6751_ = lean_ctor_get(v___x_6725_, 0);
                                v_isSharedCheck_6758_ = (!lean_is_exclusive(v___x_6725_)) as u8;
                                if v_isSharedCheck_6758_ == 0 {
                                    v___x_6753_ = v___x_6725_;
                                    v_isShared_6754_ = v_isSharedCheck_6758_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_6751_);
                                    lean_dec(v___x_6725_);
                                    v___x_6753_ = lean_box(0);
                                    v_isShared_6754_ = v_isSharedCheck_6758_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_6691_);
                            lean_dec(v_variablesKept_6650_);
                            lean_dec(v_fst_6647_);
                            lean_del_object(v___x_6645_);
                            lean_dec(v_tail_6643_);
                            lean_dec(v_x_6631_);
                            lean_dec(v_gs_6629_);
                            v_a_6759_ = lean_ctor_get(v___x_6718_, 0);
                            v_isSharedCheck_6766_ = (!lean_is_exclusive(v___x_6718_)) as u8;
                            if v_isSharedCheck_6766_ == 0 {
                                v___x_6761_ = v___x_6718_;
                                v_isShared_6762_ = v_isSharedCheck_6766_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_6759_);
                                lean_dec(v___x_6718_);
                                v___x_6761_ = lean_box(0);
                                v_isShared_6762_ = v_isSharedCheck_6766_;
                                state = 18;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                lean_inc(v_fst_6653_);
                lean_inc(v_gs_6629_);
                v___f_6659_ = lean_alloc_closure(l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_6659_, 0, v_gs_6629_);
                lean_closure_set(v___f_6659_, 1, v_variablesKept_6650_);
                lean_closure_set(v___f_6659_, 2, v_snd_6654_);
                lean_closure_set(v___f_6659_, 3, v_fst_6647_);
                lean_closure_set(v___f_6659_, 4, v_fst_6653_);
                v___x_6660_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_nthConstructor_spec__0___redArg(v_fst_6653_, v___f_6659_, v___y_6655_, v___y_6656_, v___y_6657_, v___y_6658_);
                if lean_obj_tag(v___x_6660_) == 0 {
                    v_a_6661_ = lean_ctor_get(v___x_6660_, 0);
                    lean_inc(v_a_6661_);
                    lean_dec_ref_known(v___x_6660_, 1);
                    if v_isShared_6646_ == 0 {
                        lean_ctor_set(v___x_6645_, 1, v_x_6631_);
                        lean_ctor_set(v___x_6645_, 0, v_a_6661_);
                        v___x_6663_ = v___x_6645_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6665_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6665_, 0, v_a_6661_);
                        lean_ctor_set(v_reuseFailAlloc_6665_, 1, v_x_6631_);
                        v___x_6663_ = v_reuseFailAlloc_6665_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6645_);
                    lean_dec(v_tail_6643_);
                    lean_dec(v_x_6631_);
                    lean_dec(v_gs_6629_);
                    v_a_6666_ = lean_ctor_get(v___x_6660_, 0);
                    v_isSharedCheck_6673_ = (!lean_is_exclusive(v___x_6660_)) as u8;
                    if v_isSharedCheck_6673_ == 0 {
                        v___x_6668_ = v___x_6660_;
                        v_isShared_6669_ = v_isSharedCheck_6673_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6666_);
                        lean_dec(v___x_6660_);
                        v___x_6668_ = lean_box(0);
                        v_isShared_6669_ = v_isSharedCheck_6673_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_x_6630_ = v_tail_6643_;
                v_x_6631_ = v___x_6663_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_6669_ == 0 {
                    v___x_6671_ = v___x_6668_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6672_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6672_, 0, v_a_6666_);
                    v___x_6671_ = v_reuseFailAlloc_6672_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6671_;
            }
            6 => {
                if v_isShared_6686_ == 0 {
                    v___x_6688_ = v___x_6685_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6689_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6689_, 0, v_a_6683_);
                    v___x_6688_ = v_reuseFailAlloc_6689_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6688_;
            }
            8 => {
                if v_isShared_6705_ == 0 {
                    v___x_6707_ = v___x_6704_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6708_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6708_, 0, v_a_6702_);
                    v___x_6707_ = v_reuseFailAlloc_6708_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6707_;
            }
            10 => {
                if v_isShared_6713_ == 0 {
                    v___x_6715_ = v___x_6712_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6716_, 0, v_a_6710_);
                    v___x_6715_ = v_reuseFailAlloc_6716_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6715_;
            }
            12 => {
                if v_isShared_6738_ == 0 {
                    v___x_6740_ = v___x_6737_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6741_, 0, v_a_6735_);
                    v___x_6740_ = v_reuseFailAlloc_6741_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6740_;
            }
            14 => {
                if v_isShared_6746_ == 0 {
                    v___x_6748_ = v___x_6745_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6749_, 0, v_a_6743_);
                    v___x_6748_ = v_reuseFailAlloc_6749_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6748_;
            }
            16 => {
                if v_isShared_6754_ == 0 {
                    v___x_6756_ = v___x_6753_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6757_, 0, v_a_6751_);
                    v___x_6756_ = v_reuseFailAlloc_6757_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6756_;
            }
            18 => {
                if v_isShared_6762_ == 0 {
                    v___x_6764_ = v___x_6761_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6765_, 0, v_a_6759_);
                    v___x_6764_ = v_reuseFailAlloc_6765_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___boxed(
    mut v_gs_6769_: *mut LeanObject,
    mut v_x_6770_: *mut LeanObject,
    mut v_x_6771_: *mut LeanObject,
    mut v___y_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
    mut v___y_6775_: *mut LeanObject,
    mut v___y_6776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6777_: *mut LeanObject = core::ptr::null_mut();
    v_res_6777_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_6769_, v_x_6770_, v_x_6771_, v___y_6772_, v___y_6773_, v___y_6774_, v___y_6775_);
    lean_dec(v___y_6775_);
    lean_dec_ref(v___y_6774_);
    lean_dec(v___y_6773_);
    lean_dec_ref(v___y_6772_);
    return v_res_6777_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(
    mut v_mvar_6778_: *mut LeanObject,
    mut v_cs_6779_: *mut LeanObject,
    mut v_gs_6780_: *mut LeanObject,
    mut v_s_6781_: *mut LeanObject,
    mut v_h_6782_: *mut LeanObject,
    mut v_a_6783_: *mut LeanObject,
    mut v_a_6784_: *mut LeanObject,
    mut v_a_6785_: *mut LeanObject,
    mut v_a_6786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_6790_: u8 = 0;
    let mut v___x_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: u8 = 0;
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6797_: u8 = 0;
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6802_: u8 = 0;
    let mut v_unused_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6807_: u8 = 0;
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6811_: u8 = 0;
    let mut v_one_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6822_: u8 = 0;
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6827_: u8 = 0;
    let mut v_unused_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6832_: u8 = 0;
    let mut v___x_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6836_: u8 = 0;
    let mut v_a_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6840_: u8 = 0;
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6788_ = l_List_lengthTR___redArg(v_s_6781_);
                v_zero_6789_ = lean_unsigned_to_nat(0);
                v_isZero_6790_ = lean_nat_dec_eq(v___x_6788_, v_zero_6789_);
                if v_isZero_6790_ == 1 {
                    lean_dec(v___x_6788_);
                    lean_dec(v_s_6781_);
                    lean_dec(v_gs_6780_);
                    lean_dec(v_cs_6779_);
                    v___x_6791_ =
                        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases___closed__0;
                    v___x_6792_ = 0;
                    v___x_6793_ = lean_box(0);
                    v___x_6794_ = l_Lean_MVarId_cases(
                        v_mvar_6778_,
                        v_h_6782_,
                        v___x_6791_,
                        v___x_6792_,
                        v___x_6793_,
                        v_a_6783_,
                        v_a_6784_,
                        v_a_6785_,
                        v_a_6786_,
                    );
                    if lean_obj_tag(v___x_6794_) == 0 {
                        v_isSharedCheck_6802_ = (!lean_is_exclusive(v___x_6794_)) as u8;
                        if v_isSharedCheck_6802_ == 0 {
                            v_unused_6803_ = lean_ctor_get(v___x_6794_, 0);
                            lean_dec(v_unused_6803_);
                            v___x_6796_ = v___x_6794_;
                            v_isShared_6797_ = v_isSharedCheck_6802_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_6794_);
                            v___x_6796_ = lean_box(0);
                            v_isShared_6797_ = v_isSharedCheck_6802_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6804_ = lean_ctor_get(v___x_6794_, 0);
                        v_isSharedCheck_6811_ = (!lean_is_exclusive(v___x_6794_)) as u8;
                        if v_isSharedCheck_6811_ == 0 {
                            v___x_6806_ = v___x_6794_;
                            v_isShared_6807_ = v_isSharedCheck_6811_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6804_);
                            lean_dec(v___x_6794_);
                            v___x_6806_ = lean_box(0);
                            v_isShared_6807_ = v_isSharedCheck_6811_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_one_6812_ = lean_unsigned_to_nat(1);
                    v_n_6813_ = lean_nat_sub(v___x_6788_, v_one_6812_);
                    lean_dec(v___x_6788_);
                    v___x_6814_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_nCasesSum(
                        v_n_6813_,
                        v_mvar_6778_,
                        v_h_6782_,
                        v_a_6783_,
                        v_a_6784_,
                        v_a_6785_,
                        v_a_6786_,
                    );
                    lean_dec(v_n_6813_);
                    if lean_obj_tag(v___x_6814_) == 0 {
                        v_a_6815_ = lean_ctor_get(v___x_6814_, 0);
                        lean_inc(v_a_6815_);
                        lean_dec_ref_known(v___x_6814_, 1);
                        v___x_6816_ = l_List_zipWith___at___00List_zip_spec__0(
                            lean_box(0),
                            lean_box(0),
                            v_a_6815_,
                            v_s_6781_,
                        );
                        v___x_6817_ = l_List_zipWith___at___00List_zip_spec__0(
                            lean_box(0),
                            lean_box(0),
                            v_cs_6779_,
                            v___x_6816_,
                        );
                        v___x_6818_ = lean_box(0);
                        v___x_6819_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5(v_gs_6780_, v___x_6817_, v___x_6818_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_);
                        if lean_obj_tag(v___x_6819_) == 0 {
                            v_isSharedCheck_6827_ = (!lean_is_exclusive(v___x_6819_)) as u8;
                            if v_isSharedCheck_6827_ == 0 {
                                v_unused_6828_ = lean_ctor_get(v___x_6819_, 0);
                                lean_dec(v_unused_6828_);
                                v___x_6821_ = v___x_6819_;
                                v_isShared_6822_ = v_isSharedCheck_6827_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_6819_);
                                v___x_6821_ = lean_box(0);
                                v_isShared_6822_ = v_isSharedCheck_6827_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_6829_ = lean_ctor_get(v___x_6819_, 0);
                            v_isSharedCheck_6836_ = (!lean_is_exclusive(v___x_6819_)) as u8;
                            if v_isSharedCheck_6836_ == 0 {
                                v___x_6831_ = v___x_6819_;
                                v_isShared_6832_ = v_isSharedCheck_6836_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_6829_);
                                lean_dec(v___x_6819_);
                                v___x_6831_ = lean_box(0);
                                v_isShared_6832_ = v_isSharedCheck_6836_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_s_6781_);
                        lean_dec(v_gs_6780_);
                        lean_dec(v_cs_6779_);
                        v_a_6837_ = lean_ctor_get(v___x_6814_, 0);
                        v_isSharedCheck_6844_ = (!lean_is_exclusive(v___x_6814_)) as u8;
                        if v_isSharedCheck_6844_ == 0 {
                            v___x_6839_ = v___x_6814_;
                            v_isShared_6840_ = v_isSharedCheck_6844_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6837_);
                            lean_dec(v___x_6814_);
                            v___x_6839_ = lean_box(0);
                            v_isShared_6840_ = v_isSharedCheck_6844_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6798_ = lean_box(0);
                if v_isShared_6797_ == 0 {
                    lean_ctor_set(v___x_6796_, 0, v___x_6798_);
                    v___x_6800_ = v___x_6796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6801_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6801_, 0, v___x_6798_);
                    v___x_6800_ = v_reuseFailAlloc_6801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6800_;
            }
            3 => {
                if v_isShared_6807_ == 0 {
                    v___x_6809_ = v___x_6806_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_a_6804_);
                    v___x_6809_ = v_reuseFailAlloc_6810_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6809_;
            }
            5 => {
                v___x_6823_ = lean_box(0);
                if v_isShared_6822_ == 0 {
                    lean_ctor_set(v___x_6821_, 0, v___x_6823_);
                    v___x_6825_ = v___x_6821_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6826_, 0, v___x_6823_);
                    v___x_6825_ = v_reuseFailAlloc_6826_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6825_;
            }
            7 => {
                if v_isShared_6832_ == 0 {
                    v___x_6834_ = v___x_6831_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6835_, 0, v_a_6829_);
                    v___x_6834_ = v_reuseFailAlloc_6835_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6834_;
            }
            9 => {
                if v_isShared_6840_ == 0 {
                    v___x_6842_ = v___x_6839_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6837_);
                    v___x_6842_ = v_reuseFailAlloc_6843_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive___boxed(
    mut v_mvar_6845_: *mut LeanObject,
    mut v_cs_6846_: *mut LeanObject,
    mut v_gs_6847_: *mut LeanObject,
    mut v_s_6848_: *mut LeanObject,
    mut v_h_6849_: *mut LeanObject,
    mut v_a_6850_: *mut LeanObject,
    mut v_a_6851_: *mut LeanObject,
    mut v_a_6852_: *mut LeanObject,
    mut v_a_6853_: *mut LeanObject,
    mut v_a_6854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6855_: *mut LeanObject = core::ptr::null_mut();
    v_res_6855_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(
        v_mvar_6845_,
        v_cs_6846_,
        v_gs_6847_,
        v_s_6848_,
        v_h_6849_,
        v_a_6850_,
        v_a_6851_,
        v_a_6852_,
        v_a_6853_,
    );
    lean_dec(v_a_6853_);
    lean_dec_ref(v_a_6852_);
    lean_dec(v_a_6851_);
    lean_dec_ref(v_a_6850_);
    return v_res_6855_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(
    mut v_type_6856_: *mut LeanObject,
    mut v_k_6857_: *mut LeanObject,
    mut v_cleanupAnnotations_6858_: u8,
    mut v_whnfType_6859_: u8,
    mut v___y_6860_: *mut LeanObject,
    mut v___y_6861_: *mut LeanObject,
    mut v___y_6862_: *mut LeanObject,
    mut v___y_6863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6870_: u8 = 0;
    let mut v___x_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_a_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6878_: u8 = 0;
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6865_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_6865_, 0, v_k_6857_);
                v___x_6866_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    lean_box(0),
                    v_type_6856_,
                    v___f_6865_,
                    v_cleanupAnnotations_6858_,
                    v_whnfType_6859_,
                    v___y_6860_,
                    v___y_6861_,
                    v___y_6862_,
                    v___y_6863_,
                );
                if lean_obj_tag(v___x_6866_) == 0 {
                    v_a_6867_ = lean_ctor_get(v___x_6866_, 0);
                    v_isSharedCheck_6874_ = (!lean_is_exclusive(v___x_6866_)) as u8;
                    if v_isSharedCheck_6874_ == 0 {
                        v___x_6869_ = v___x_6866_;
                        v_isShared_6870_ = v_isSharedCheck_6874_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6867_);
                        lean_dec(v___x_6866_);
                        v___x_6869_ = lean_box(0);
                        v_isShared_6870_ = v_isSharedCheck_6874_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6875_ = lean_ctor_get(v___x_6866_, 0);
                    v_isSharedCheck_6882_ = (!lean_is_exclusive(v___x_6866_)) as u8;
                    if v_isSharedCheck_6882_ == 0 {
                        v___x_6877_ = v___x_6866_;
                        v_isShared_6878_ = v_isSharedCheck_6882_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6875_);
                        lean_dec(v___x_6866_);
                        v___x_6877_ = lean_box(0);
                        v_isShared_6878_ = v_isSharedCheck_6882_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6870_ == 0 {
                    v___x_6872_ = v___x_6869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6873_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_a_6867_);
                    v___x_6872_ = v_reuseFailAlloc_6873_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6872_;
            }
            3 => {
                if v_isShared_6878_ == 0 {
                    v___x_6880_ = v___x_6877_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6881_, 0, v_a_6875_);
                    v___x_6880_ = v_reuseFailAlloc_6881_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg___boxed(
    mut v_type_6883_: *mut LeanObject,
    mut v_k_6884_: *mut LeanObject,
    mut v_cleanupAnnotations_6885_: *mut LeanObject,
    mut v_whnfType_6886_: *mut LeanObject,
    mut v___y_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6892_: u8 = 0;
    let mut v_whnfType_boxed_6893_: u8 = 0;
    let mut v_res_6894_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6892_ = (lean_unbox(v_cleanupAnnotations_6885_) as u8);
    v_whnfType_boxed_6893_ = (lean_unbox(v_whnfType_6886_) as u8);
    v_res_6894_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_6883_, v_k_6884_, v_cleanupAnnotations_boxed_6892_, v_whnfType_boxed_6893_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_);
    lean_dec(v___y_6890_);
    lean_dec_ref(v___y_6889_);
    lean_dec(v___y_6888_);
    lean_dec_ref(v___y_6887_);
    return v_res_6894_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(
    mut v_00_u03b1_6895_: *mut LeanObject,
    mut v_type_6896_: *mut LeanObject,
    mut v_k_6897_: *mut LeanObject,
    mut v_cleanupAnnotations_6898_: u8,
    mut v_whnfType_6899_: u8,
    mut v___y_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    v___x_6905_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_6896_, v_k_6897_, v_cleanupAnnotations_6898_, v_whnfType_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_);
    return v___x_6905_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___boxed(
    mut v_00_u03b1_6906_: *mut LeanObject,
    mut v_type_6907_: *mut LeanObject,
    mut v_k_6908_: *mut LeanObject,
    mut v_cleanupAnnotations_6909_: *mut LeanObject,
    mut v_whnfType_6910_: *mut LeanObject,
    mut v___y_6911_: *mut LeanObject,
    mut v___y_6912_: *mut LeanObject,
    mut v___y_6913_: *mut LeanObject,
    mut v___y_6914_: *mut LeanObject,
    mut v___y_6915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_6916_: u8 = 0;
    let mut v_whnfType_boxed_6917_: u8 = 0;
    let mut v_res_6918_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_6916_ = (lean_unbox(v_cleanupAnnotations_6909_) as u8);
    v_whnfType_boxed_6917_ = (lean_unbox(v_whnfType_6910_) as u8);
    v_res_6918_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1(v_00_u03b1_6906_, v_type_6907_, v_k_6908_, v_cleanupAnnotations_boxed_6916_, v_whnfType_boxed_6917_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_);
    lean_dec(v___y_6914_);
    lean_dec_ref(v___y_6913_);
    lean_dec(v___y_6912_);
    lean_dec_ref(v___y_6911_);
    return v_res_6918_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(
    mut v_e_6919_: *mut LeanObject,
    mut v___y_6920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6922_: u8 = 0;
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6936_: u8 = 0;
    let mut v___x_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6942_: u8 = 0;
    let mut v_unused_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6922_ = l_Lean_Expr_hasMVar(v_e_6919_);
                if v___x_6922_ == 0 {
                    v___x_6923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6923_, 0, v_e_6919_);
                    return v___x_6923_;
                } else {
                    v___x_6924_ = lean_st_ref_get(v___y_6920_);
                    v_mctx_6925_ = lean_ctor_get(v___x_6924_, 0);
                    lean_inc_ref(v_mctx_6925_);
                    lean_dec(v___x_6924_);
                    v___x_6926_ = l_Lean_instantiateMVarsCore(v_mctx_6925_, v_e_6919_);
                    v_fst_6927_ = lean_ctor_get(v___x_6926_, 0);
                    lean_inc(v_fst_6927_);
                    v_snd_6928_ = lean_ctor_get(v___x_6926_, 1);
                    lean_inc(v_snd_6928_);
                    lean_dec_ref(v___x_6926_);
                    v___x_6929_ = lean_st_ref_take(v___y_6920_);
                    v_cache_6930_ = lean_ctor_get(v___x_6929_, 1);
                    v_zetaDeltaFVarIds_6931_ = lean_ctor_get(v___x_6929_, 2);
                    v_postponed_6932_ = lean_ctor_get(v___x_6929_, 3);
                    v_diag_6933_ = lean_ctor_get(v___x_6929_, 4);
                    v_isSharedCheck_6942_ = (!lean_is_exclusive(v___x_6929_)) as u8;
                    if v_isSharedCheck_6942_ == 0 {
                        v_unused_6943_ = lean_ctor_get(v___x_6929_, 0);
                        lean_dec(v_unused_6943_);
                        v___x_6935_ = v___x_6929_;
                        v_isShared_6936_ = v_isSharedCheck_6942_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_6933_);
                        lean_inc(v_postponed_6932_);
                        lean_inc(v_zetaDeltaFVarIds_6931_);
                        lean_inc(v_cache_6930_);
                        lean_dec(v___x_6929_);
                        v___x_6935_ = lean_box(0);
                        v_isShared_6936_ = v_isSharedCheck_6942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6936_ == 0 {
                    lean_ctor_set(v___x_6935_, 0, v_snd_6928_);
                    v___x_6938_ = v___x_6935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6941_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6941_, 0, v_snd_6928_);
                    lean_ctor_set(v_reuseFailAlloc_6941_, 1, v_cache_6930_);
                    lean_ctor_set(v_reuseFailAlloc_6941_, 2, v_zetaDeltaFVarIds_6931_);
                    lean_ctor_set(v_reuseFailAlloc_6941_, 3, v_postponed_6932_);
                    lean_ctor_set(v_reuseFailAlloc_6941_, 4, v_diag_6933_);
                    v___x_6938_ = v_reuseFailAlloc_6941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6939_ = lean_st_ref_set(v___y_6920_, v___x_6938_);
                v___x_6940_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6940_, 0, v_fst_6927_);
                return v___x_6940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg___boxed(
    mut v_e_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6947_: *mut LeanObject = core::ptr::null_mut();
    v_res_6947_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_6944_, v___y_6945_);
    lean_dec(v___y_6945_);
    return v_res_6947_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(
    mut v_e_6948_: *mut LeanObject,
    mut v___y_6949_: *mut LeanObject,
    mut v___y_6950_: *mut LeanObject,
    mut v___y_6951_: *mut LeanObject,
    mut v___y_6952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    v___x_6954_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_e_6948_, v___y_6950_);
    return v___x_6954_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___boxed(
    mut v_e_6955_: *mut LeanObject,
    mut v___y_6956_: *mut LeanObject,
    mut v___y_6957_: *mut LeanObject,
    mut v___y_6958_: *mut LeanObject,
    mut v___y_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6961_: *mut LeanObject = core::ptr::null_mut();
    v_res_6961_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3(v_e_6955_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_);
    lean_dec(v___y_6959_);
    lean_dec_ref(v___y_6958_);
    lean_dec(v___y_6957_);
    lean_dec_ref(v___y_6956_);
    return v_res_6961_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(
    mut v_thm_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_all_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6971_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: u8 = 0;
    let mut v___x_6981_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6965_ = lean_st_ref_get(v___y_6963_);
                v_env_6966_ = lean_ctor_get(v___x_6965_, 0);
                lean_inc_ref_n(v_env_6966_, 2);
                lean_dec(v___x_6965_);
                v_toConstantVal_6967_ = lean_ctor_get(v_thm_6962_, 0);
                v_value_6968_ = lean_ctor_get(v_thm_6962_, 1);
                v_all_6969_ = lean_ctor_get(v_thm_6962_, 2);
                v_type_6979_ = lean_ctor_get(v_toConstantVal_6967_, 2);
                v___x_6980_ = l_Lean_Environment_hasUnsafe(v_env_6966_, v_type_6979_);
                if v___x_6980_ == 0 {
                    v___x_6981_ = l_Lean_Environment_hasUnsafe(v_env_6966_, v_value_6968_);
                    v___y_6971_ = v___x_6981_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_env_6966_);
                    v___y_6971_ = v___x_6980_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_6971_ == 0 {
                    v___x_6972_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v___x_6972_, 0, v_thm_6962_);
                    v___x_6973_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6973_, 0, v___x_6972_);
                    return v___x_6973_;
                } else {
                    lean_inc(v_all_6969_);
                    lean_inc_ref(v_value_6968_);
                    lean_inc_ref(v_toConstantVal_6967_);
                    lean_dec_ref(v_thm_6962_);
                    v___x_6974_ = lean_box(0);
                    v___x_6975_ = 0;
                    v___x_6976_ = lean_alloc_ctor(0, 4, (1) as u32);
                    lean_ctor_set(v___x_6976_, 0, v_toConstantVal_6967_);
                    lean_ctor_set(v___x_6976_, 1, v_value_6968_);
                    lean_ctor_set(v___x_6976_, 2, v___x_6974_);
                    lean_ctor_set(v___x_6976_, 3, v_all_6969_);
                    lean_ctor_set_uint8(
                        v___x_6976_,
                        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                        v___x_6975_,
                    );
                    v___x_6977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6977_, 0, v___x_6976_);
                    v___x_6978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6978_, 0, v___x_6977_);
                    return v___x_6978_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg___boxed(
    mut v_thm_6982_: *mut LeanObject,
    mut v___y_6983_: *mut LeanObject,
    mut v___y_6984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6985_: *mut LeanObject = core::ptr::null_mut();
    v_res_6985_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_6982_, v___y_6983_);
    lean_dec(v___y_6983_);
    return v_res_6985_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(
    mut v_thm_6986_: *mut LeanObject,
    mut v___y_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
    mut v___y_6990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6992_: *mut LeanObject = core::ptr::null_mut();
    v___x_6992_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v_thm_6986_, v___y_6990_);
    return v___x_6992_;
}
pub unsafe fn l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___boxed(
    mut v_thm_6993_: *mut LeanObject,
    mut v___y_6994_: *mut LeanObject,
    mut v___y_6995_: *mut LeanObject,
    mut v___y_6996_: *mut LeanObject,
    mut v___y_6997_: *mut LeanObject,
    mut v___y_6998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6999_: *mut LeanObject = core::ptr::null_mut();
    v_res_6999_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4(v_thm_6993_, v___y_6994_, v___y_6995_, v___y_6996_, v___y_6997_);
    lean_dec(v___y_6997_);
    lean_dec_ref(v___y_6996_);
    lean_dec(v___y_6995_);
    lean_dec_ref(v___y_6994_);
    return v_res_6999_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(
    mut v_name_7000_: *mut LeanObject,
    mut v_levelParams_7001_: *mut LeanObject,
    mut v_type_7002_: *mut LeanObject,
    mut v_value_7003_: *mut LeanObject,
    mut v_hints_7004_: *mut LeanObject,
    mut v___y_7005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7009_: u8 = 0;
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7016_: u8 = 0;
    let mut v___x_7017_: u8 = 0;
    let mut v___x_7018_: u8 = 0;
    let mut v_env_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: u8 = 0;
    let mut v___x_7021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7007_ = lean_st_ref_get(v___y_7005_);
                v_env_7019_ = lean_ctor_get(v___x_7007_, 0);
                lean_inc_ref_n(v_env_7019_, 2);
                lean_dec(v___x_7007_);
                v___x_7020_ = l_Lean_Environment_hasUnsafe(v_env_7019_, v_type_7002_);
                if v___x_7020_ == 0 {
                    v___x_7021_ = l_Lean_Environment_hasUnsafe(v_env_7019_, v_value_7003_);
                    v___y_7016_ = v___x_7021_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_7019_);
                    v___y_7016_ = v___x_7020_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v_name_7000_);
                v___x_7010_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_7010_, 0, v_name_7000_);
                lean_ctor_set(v___x_7010_, 1, v_levelParams_7001_);
                lean_ctor_set(v___x_7010_, 2, v_type_7002_);
                v___x_7011_ = lean_box(0);
                v___x_7012_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_7012_, 0, v_name_7000_);
                lean_ctor_set(v___x_7012_, 1, v___x_7011_);
                v___x_7013_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_7013_, 0, v___x_7010_);
                lean_ctor_set(v___x_7013_, 1, v_value_7003_);
                lean_ctor_set(v___x_7013_, 2, v_hints_7004_);
                lean_ctor_set(v___x_7013_, 3, v___x_7012_);
                lean_ctor_set_uint8(
                    v___x_7013_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_7009_,
                );
                v___x_7014_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7014_, 0, v___x_7013_);
                return v___x_7014_;
            }
            2 => {
                if v___y_7016_ == 0 {
                    v___x_7017_ = 1;
                    v___y_7009_ = v___x_7017_;
                    state = 1;
                    continue;
                } else {
                    v___x_7018_ = 0;
                    v___y_7009_ = v___x_7018_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg___boxed(
    mut v_name_7022_: *mut LeanObject,
    mut v_levelParams_7023_: *mut LeanObject,
    mut v_type_7024_: *mut LeanObject,
    mut v_value_7025_: *mut LeanObject,
    mut v_hints_7026_: *mut LeanObject,
    mut v___y_7027_: *mut LeanObject,
    mut v___y_7028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7029_: *mut LeanObject = core::ptr::null_mut();
    v_res_7029_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_7022_, v_levelParams_7023_, v_type_7024_, v_value_7025_, v_hints_7026_, v___y_7027_);
    lean_dec(v___y_7027_);
    return v_res_7029_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(
    mut v_name_7030_: *mut LeanObject,
    mut v_levelParams_7031_: *mut LeanObject,
    mut v_type_7032_: *mut LeanObject,
    mut v_value_7033_: *mut LeanObject,
    mut v_hints_7034_: *mut LeanObject,
    mut v___y_7035_: *mut LeanObject,
    mut v___y_7036_: *mut LeanObject,
    mut v___y_7037_: *mut LeanObject,
    mut v___y_7038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7040_: *mut LeanObject = core::ptr::null_mut();
    v___x_7040_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v_name_7030_, v_levelParams_7031_, v_type_7032_, v_value_7033_, v_hints_7034_, v___y_7038_);
    return v___x_7040_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___boxed(
    mut v_name_7041_: *mut LeanObject,
    mut v_levelParams_7042_: *mut LeanObject,
    mut v_type_7043_: *mut LeanObject,
    mut v_value_7044_: *mut LeanObject,
    mut v_hints_7045_: *mut LeanObject,
    mut v___y_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7051_: *mut LeanObject = core::ptr::null_mut();
    v_res_7051_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5(v_name_7041_, v_levelParams_7042_, v_type_7043_, v_value_7044_, v_hints_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_);
    lean_dec(v___y_7049_);
    lean_dec_ref(v___y_7048_);
    lean_dec(v___y_7047_);
    lean_dec_ref(v___y_7046_);
    return v_res_7051_;
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(
    mut v_univs_7052_: *mut LeanObject,
    mut v___x_7053_: *mut LeanObject,
    mut v___x_7054_: *mut LeanObject,
    mut v_x_7055_: *mut LeanObject,
    mut v_x_7056_: *mut LeanObject,
    mut v___y_7057_: *mut LeanObject,
    mut v___y_7058_: *mut LeanObject,
    mut v___y_7059_: *mut LeanObject,
    mut v___y_7060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7068_: u8 = 0;
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7078_: u8 = 0;
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7082_: u8 = 0;
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7055_) == 0 {
                    lean_dec(v___x_7054_);
                    lean_dec(v___x_7053_);
                    lean_dec(v_univs_7052_);
                    v___x_7062_ = l_List_reverse___redArg(v_x_7056_);
                    v___x_7063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7063_, 0, v___x_7062_);
                    return v___x_7063_;
                } else {
                    v_head_7064_ = lean_ctor_get(v_x_7055_, 0);
                    v_tail_7065_ = lean_ctor_get(v_x_7055_, 1);
                    v_isSharedCheck_7083_ = (!lean_is_exclusive(v_x_7055_)) as u8;
                    if v_isSharedCheck_7083_ == 0 {
                        v___x_7067_ = v_x_7055_;
                        v_isShared_7068_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7065_);
                        lean_inc(v_head_7064_);
                        lean_dec(v_x_7055_);
                        v___x_7067_ = lean_box(0);
                        v_isShared_7068_ = v_isSharedCheck_7083_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_7054_);
                lean_inc(v___x_7053_);
                lean_inc(v_univs_7052_);
                v___x_7069_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp(
                    v_univs_7052_,
                    v___x_7053_,
                    v___x_7054_,
                    v_head_7064_,
                    v___y_7057_,
                    v___y_7058_,
                    v___y_7059_,
                    v___y_7060_,
                );
                if lean_obj_tag(v___x_7069_) == 0 {
                    v_a_7070_ = lean_ctor_get(v___x_7069_, 0);
                    lean_inc(v_a_7070_);
                    lean_dec_ref_known(v___x_7069_, 1);
                    if v_isShared_7068_ == 0 {
                        lean_ctor_set(v___x_7067_, 1, v_x_7056_);
                        lean_ctor_set(v___x_7067_, 0, v_a_7070_);
                        v___x_7072_ = v___x_7067_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7074_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_a_7070_);
                        lean_ctor_set(v_reuseFailAlloc_7074_, 1, v_x_7056_);
                        v___x_7072_ = v_reuseFailAlloc_7074_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7067_);
                    lean_dec(v_tail_7065_);
                    lean_dec(v_x_7056_);
                    lean_dec(v___x_7054_);
                    lean_dec(v___x_7053_);
                    lean_dec(v_univs_7052_);
                    v_a_7075_ = lean_ctor_get(v___x_7069_, 0);
                    v_isSharedCheck_7082_ = (!lean_is_exclusive(v___x_7069_)) as u8;
                    if v_isSharedCheck_7082_ == 0 {
                        v___x_7077_ = v___x_7069_;
                        v_isShared_7078_ = v_isSharedCheck_7082_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7075_);
                        lean_dec(v___x_7069_);
                        v___x_7077_ = lean_box(0);
                        v_isShared_7078_ = v_isSharedCheck_7082_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_7055_ = v_tail_7065_;
                v_x_7056_ = v___x_7072_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_7078_ == 0 {
                    v___x_7080_ = v___x_7077_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7081_, 0, v_a_7075_);
                    v___x_7080_ = v_reuseFailAlloc_7081_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0___boxed(
    mut v_univs_7084_: *mut LeanObject,
    mut v___x_7085_: *mut LeanObject,
    mut v___x_7086_: *mut LeanObject,
    mut v_x_7087_: *mut LeanObject,
    mut v_x_7088_: *mut LeanObject,
    mut v___y_7089_: *mut LeanObject,
    mut v___y_7090_: *mut LeanObject,
    mut v___y_7091_: *mut LeanObject,
    mut v___y_7092_: *mut LeanObject,
    mut v___y_7093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7094_: *mut LeanObject = core::ptr::null_mut();
    v_res_7094_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_7084_, v___x_7085_, v___x_7086_, v_x_7087_, v_x_7088_, v___y_7089_, v___y_7090_, v___y_7091_, v___y_7092_);
    lean_dec(v___y_7092_);
    lean_dec_ref(v___y_7091_);
    lean_dec(v___y_7090_);
    lean_dec_ref(v___y_7089_);
    return v_res_7094_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    v___x_7099_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__2;
    v___x_7100_ = l_Lean_stringToMessageData(v___x_7099_);
    return v___x_7100_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(
    mut v_name_7101_: *mut LeanObject,
    mut v_univs_7102_: *mut LeanObject,
    mut v_numParams_7103_: *mut LeanObject,
    mut v_ctors_7104_: *mut LeanObject,
    mut v___x_7105_: *mut LeanObject,
    mut v_fvars_7106_: *mut LeanObject,
    mut v_ty_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvars_x27_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7128_: u8 = 0;
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: u8 = 0;
    let mut v___x_7131_: u8 = 0;
    let mut v___x_7132_: u8 = 0;
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7142_: u8 = 0;
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7150_: u8 = 0;
    let mut v_a_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7154_: u8 = 0;
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7158_: u8 = 0;
    let mut v_a_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7162_: u8 = 0;
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7166_: u8 = 0;
    let mut v_isSharedCheck_7167_: u8 = 0;
    let mut v_a_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7171_: u8 = 0;
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7175_: u8 = 0;
    let mut v___x_7176_: u8 = 0;
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7182_: u8 = 0;
    let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7176_ = l_Lean_Expr_isProp(v_ty_7107_);
                if v___x_7176_ == 0 {
                    lean_dec_ref(v_fvars_7106_);
                    lean_dec(v___x_7105_);
                    lean_dec(v_ctors_7104_);
                    lean_dec(v_numParams_7103_);
                    lean_dec(v_univs_7102_);
                    lean_dec(v_name_7101_);
                    v___x_7177_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__3);
                    v___x_7178_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_7177_, v___y_7108_, v___y_7109_, v___y_7110_, v___y_7111_);
                    v_a_7179_ = lean_ctor_get(v___x_7178_, 0);
                    v_isSharedCheck_7186_ = (!lean_is_exclusive(v___x_7178_)) as u8;
                    if v_isSharedCheck_7186_ == 0 {
                        v___x_7181_ = v___x_7178_;
                        v_isShared_7182_ = v_isSharedCheck_7186_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_7179_);
                        lean_dec(v___x_7178_);
                        v___x_7181_ = lean_box(0);
                        v_isShared_7182_ = v_isSharedCheck_7186_;
                        state = 12;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_univs_7102_);
                v___x_7114_ = l_Lean_mkConst(v_name_7101_, v_univs_7102_);
                v_lhs_7115_ = l_Lean_mkAppN(v___x_7114_, v_fvars_7106_);
                lean_inc_ref(v_fvars_7106_);
                v_fvars_x27_7116_ = lean_array_to_list(v_fvars_7106_);
                v___x_7117_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp___lam__1___closed__1;
                lean_inc(v_numParams_7103_);
                lean_inc(v_fvars_x27_7116_);
                v___x_7118_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                    lean_box(0),
                    v_fvars_x27_7116_,
                    v_fvars_x27_7116_,
                    v_numParams_7103_,
                    v___x_7117_,
                );
                v___x_7119_ = l_List_drop___redArg(v_numParams_7103_, v_fvars_x27_7116_);
                lean_dec(v_fvars_x27_7116_);
                v___x_7120_ = lean_box(0);
                v___x_7121_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__0(v_univs_7102_, v___x_7118_, v___x_7119_, v_ctors_7104_, v___x_7120_, v___y_7108_, v___y_7109_, v___y_7110_, v___y_7111_);
                if lean_obj_tag(v___x_7121_) == 0 {
                    v_a_7122_ = lean_ctor_get(v___x_7121_, 0);
                    lean_inc(v_a_7122_);
                    lean_dec_ref_known(v___x_7121_, 1);
                    v___x_7123_ = l_List_unzipTR___redArg(v_a_7122_);
                    v_fst_7124_ = lean_ctor_get(v___x_7123_, 0);
                    v_snd_7125_ = lean_ctor_get(v___x_7123_, 1);
                    v_isSharedCheck_7167_ = (!lean_is_exclusive(v___x_7123_)) as u8;
                    if v_isSharedCheck_7167_ == 0 {
                        v___x_7127_ = v___x_7123_;
                        v_isShared_7128_ = v_isSharedCheck_7167_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_7125_);
                        lean_inc(v_fst_7124_);
                        lean_dec(v___x_7123_);
                        v___x_7127_ = lean_box(0);
                        v_isShared_7128_ = v_isSharedCheck_7167_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_lhs_7115_);
                    lean_dec_ref(v_fvars_7106_);
                    lean_dec(v___x_7105_);
                    v_a_7168_ = lean_ctor_get(v___x_7121_, 0);
                    v_isSharedCheck_7175_ = (!lean_is_exclusive(v___x_7121_)) as u8;
                    if v_isSharedCheck_7175_ == 0 {
                        v___x_7170_ = v___x_7121_;
                        v_isShared_7171_ = v_isSharedCheck_7175_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_7168_);
                        lean_dec(v___x_7121_);
                        v___x_7170_ = lean_box(0);
                        v_isShared_7171_ = v_isSharedCheck_7175_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7129_ =
                    l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkOrList(v_snd_7125_);
                v___x_7130_ = 0;
                v___x_7131_ = 1;
                v___x_7132_ = 1;
                lean_inc_ref(v___x_7129_);
                v___x_7133_ = l_Lean_Meta_mkLambdaFVars(
                    v_fvars_7106_,
                    v___x_7129_,
                    v___x_7130_,
                    v___x_7131_,
                    v___x_7130_,
                    v___x_7131_,
                    v___x_7132_,
                    v___y_7108_,
                    v___y_7109_,
                    v___y_7110_,
                    v___y_7111_,
                );
                if lean_obj_tag(v___x_7133_) == 0 {
                    v_a_7134_ = lean_ctor_get(v___x_7133_, 0);
                    lean_inc(v_a_7134_);
                    lean_dec_ref_known(v___x_7133_, 1);
                    v___x_7135_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___closed__1;
                    v___x_7136_ = l_Lean_mkConst(v___x_7135_, v___x_7105_);
                    v___x_7137_ = l_Lean_mkAppB(v___x_7136_, v_lhs_7115_, v___x_7129_);
                    v___x_7138_ = l_Lean_Meta_mkForallFVars(
                        v_fvars_7106_,
                        v___x_7137_,
                        v___x_7130_,
                        v___x_7131_,
                        v___x_7131_,
                        v___x_7132_,
                        v___y_7108_,
                        v___y_7109_,
                        v___y_7110_,
                        v___y_7111_,
                    );
                    lean_dec_ref(v_fvars_7106_);
                    if lean_obj_tag(v___x_7138_) == 0 {
                        v_a_7139_ = lean_ctor_get(v___x_7138_, 0);
                        v_isSharedCheck_7150_ = (!lean_is_exclusive(v___x_7138_)) as u8;
                        if v_isSharedCheck_7150_ == 0 {
                            v___x_7141_ = v___x_7138_;
                            v_isShared_7142_ = v_isSharedCheck_7150_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7139_);
                            lean_dec(v___x_7138_);
                            v___x_7141_ = lean_box(0);
                            v_isShared_7142_ = v_isSharedCheck_7150_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_7134_);
                        lean_del_object(v___x_7127_);
                        lean_dec(v_fst_7124_);
                        v_a_7151_ = lean_ctor_get(v___x_7138_, 0);
                        v_isSharedCheck_7158_ = (!lean_is_exclusive(v___x_7138_)) as u8;
                        if v_isSharedCheck_7158_ == 0 {
                            v___x_7153_ = v___x_7138_;
                            v_isShared_7154_ = v_isSharedCheck_7158_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7151_);
                            lean_dec(v___x_7138_);
                            v___x_7153_ = lean_box(0);
                            v_isShared_7154_ = v_isSharedCheck_7158_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_7129_);
                    lean_del_object(v___x_7127_);
                    lean_dec(v_fst_7124_);
                    lean_dec_ref(v_lhs_7115_);
                    lean_dec_ref(v_fvars_7106_);
                    lean_dec(v___x_7105_);
                    v_a_7159_ = lean_ctor_get(v___x_7133_, 0);
                    v_isSharedCheck_7166_ = (!lean_is_exclusive(v___x_7133_)) as u8;
                    if v_isSharedCheck_7166_ == 0 {
                        v___x_7161_ = v___x_7133_;
                        v_isShared_7162_ = v_isSharedCheck_7166_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7159_);
                        lean_dec(v___x_7133_);
                        v___x_7161_ = lean_box(0);
                        v_isShared_7162_ = v_isSharedCheck_7166_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7128_ == 0 {
                    lean_ctor_set(v___x_7127_, 1, v_a_7134_);
                    v___x_7144_ = v___x_7127_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7149_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7149_, 0, v_fst_7124_);
                    lean_ctor_set(v_reuseFailAlloc_7149_, 1, v_a_7134_);
                    v___x_7144_ = v_reuseFailAlloc_7149_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7145_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7145_, 0, v_a_7139_);
                lean_ctor_set(v___x_7145_, 1, v___x_7144_);
                if v_isShared_7142_ == 0 {
                    lean_ctor_set(v___x_7141_, 0, v___x_7145_);
                    v___x_7147_ = v___x_7141_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7148_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7148_, 0, v___x_7145_);
                    v___x_7147_ = v_reuseFailAlloc_7148_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7147_;
            }
            6 => {
                if v_isShared_7154_ == 0 {
                    v___x_7156_ = v___x_7153_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7157_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7157_, 0, v_a_7151_);
                    v___x_7156_ = v_reuseFailAlloc_7157_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7156_;
            }
            8 => {
                if v_isShared_7162_ == 0 {
                    v___x_7164_ = v___x_7161_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7165_, 0, v_a_7159_);
                    v___x_7164_ = v_reuseFailAlloc_7165_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7164_;
            }
            10 => {
                if v_isShared_7171_ == 0 {
                    v___x_7173_ = v___x_7170_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7174_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7174_, 0, v_a_7168_);
                    v___x_7173_ = v_reuseFailAlloc_7174_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7173_;
            }
            12 => {
                if v_isShared_7182_ == 0 {
                    v___x_7184_ = v___x_7181_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7185_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7185_, 0, v_a_7179_);
                    v___x_7184_ = v_reuseFailAlloc_7185_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed(
    mut v_name_7187_: *mut LeanObject,
    mut v_univs_7188_: *mut LeanObject,
    mut v_numParams_7189_: *mut LeanObject,
    mut v_ctors_7190_: *mut LeanObject,
    mut v___x_7191_: *mut LeanObject,
    mut v_fvars_7192_: *mut LeanObject,
    mut v_ty_7193_: *mut LeanObject,
    mut v___y_7194_: *mut LeanObject,
    mut v___y_7195_: *mut LeanObject,
    mut v___y_7196_: *mut LeanObject,
    mut v___y_7197_: *mut LeanObject,
    mut v___y_7198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7199_: *mut LeanObject = core::ptr::null_mut();
    v_res_7199_ =
        l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0(
            v_name_7187_,
            v_univs_7188_,
            v_numParams_7189_,
            v_ctors_7190_,
            v___x_7191_,
            v_fvars_7192_,
            v_ty_7193_,
            v___y_7194_,
            v___y_7195_,
            v___y_7196_,
            v___y_7197_,
        );
    lean_dec(v___y_7197_);
    lean_dec_ref(v___y_7196_);
    lean_dec(v___y_7195_);
    lean_dec_ref(v___y_7194_);
    lean_dec_ref(v_ty_7193_);
    return v_res_7199_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(
    mut v_a_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7207_: u8 = 0;
    let mut v___x_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_7200_) == 0 {
                    v___x_7202_ = l_List_reverse___redArg(v_a_7201_);
                    return v___x_7202_;
                } else {
                    v_head_7203_ = lean_ctor_get(v_a_7200_, 0);
                    v_tail_7204_ = lean_ctor_get(v_a_7200_, 1);
                    v_isSharedCheck_7213_ = (!lean_is_exclusive(v_a_7200_)) as u8;
                    if v_isSharedCheck_7213_ == 0 {
                        v___x_7206_ = v_a_7200_;
                        v_isShared_7207_ = v_isSharedCheck_7213_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_7204_);
                        lean_inc(v_head_7203_);
                        lean_dec(v_a_7200_);
                        v___x_7206_ = lean_box(0);
                        v_isShared_7207_ = v_isSharedCheck_7213_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7208_ = l_Lean_Expr_fvar___override(v_head_7203_);
                if v_isShared_7207_ == 0 {
                    lean_ctor_set(v___x_7206_, 1, v_a_7201_);
                    lean_ctor_set(v___x_7206_, 0, v___x_7208_);
                    v___x_7210_ = v___x_7206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7212_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7212_, 0, v___x_7208_);
                    lean_ctor_set(v_reuseFailAlloc_7212_, 1, v_a_7201_);
                    v___x_7210_ = v_reuseFailAlloc_7212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7200_ = v_tail_7204_;
                v_a_7201_ = v___x_7210_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0()
-> f64 {
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: f64 = 0.0;
    v___x_7214_ = lean_unsigned_to_nat(0);
    v___x_7215_ = lean_float_of_nat(v___x_7214_);
    return v___x_7215_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(
    mut v_cls_7219_: *mut LeanObject,
    mut v_msg_7220_: *mut LeanObject,
    mut v___y_7221_: *mut LeanObject,
    mut v___y_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
    mut v___y_7224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7231_: u8 = 0;
    let mut v___x_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_7239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_7240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7244_: u8 = 0;
    let mut v_tid_7245_: u64 = 0;
    let mut v_traces_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7249_: u8 = 0;
    let mut v___x_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: f64 = 0.0;
    let mut v___x_7252_: u8 = 0;
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v_isSharedCheck_7271_: u8 = 0;
    let mut v_isSharedCheck_7272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7226_ = lean_ctor_get(v___y_7223_, 5);
                v___x_7227_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0_spec__0(v_msg_7220_, v___y_7221_, v___y_7222_, v___y_7223_, v___y_7224_);
                v_a_7228_ = lean_ctor_get(v___x_7227_, 0);
                v_isSharedCheck_7272_ = (!lean_is_exclusive(v___x_7227_)) as u8;
                if v_isSharedCheck_7272_ == 0 {
                    v___x_7230_ = v___x_7227_;
                    v_isShared_7231_ = v_isSharedCheck_7272_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7228_);
                    lean_dec(v___x_7227_);
                    v___x_7230_ = lean_box(0);
                    v_isShared_7231_ = v_isSharedCheck_7272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7232_ = lean_st_ref_take(v___y_7224_);
                v_traceState_7233_ = lean_ctor_get(v___x_7232_, 4);
                v_env_7234_ = lean_ctor_get(v___x_7232_, 0);
                v_nextMacroScope_7235_ = lean_ctor_get(v___x_7232_, 1);
                v_ngen_7236_ = lean_ctor_get(v___x_7232_, 2);
                v_auxDeclNGen_7237_ = lean_ctor_get(v___x_7232_, 3);
                v_cache_7238_ = lean_ctor_get(v___x_7232_, 5);
                v_messages_7239_ = lean_ctor_get(v___x_7232_, 6);
                v_infoState_7240_ = lean_ctor_get(v___x_7232_, 7);
                v_snapshotTasks_7241_ = lean_ctor_get(v___x_7232_, 8);
                v_isSharedCheck_7271_ = (!lean_is_exclusive(v___x_7232_)) as u8;
                if v_isSharedCheck_7271_ == 0 {
                    v___x_7243_ = v___x_7232_;
                    v_isShared_7244_ = v_isSharedCheck_7271_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_7241_);
                    lean_inc(v_infoState_7240_);
                    lean_inc(v_messages_7239_);
                    lean_inc(v_cache_7238_);
                    lean_inc(v_traceState_7233_);
                    lean_inc(v_auxDeclNGen_7237_);
                    lean_inc(v_ngen_7236_);
                    lean_inc(v_nextMacroScope_7235_);
                    lean_inc(v_env_7234_);
                    lean_dec(v___x_7232_);
                    v___x_7243_ = lean_box(0);
                    v_isShared_7244_ = v_isSharedCheck_7271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_7245_ = lean_ctor_get_uint64(
                    v_traceState_7233_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_7246_ = lean_ctor_get(v_traceState_7233_, 0);
                v_isSharedCheck_7270_ = (!lean_is_exclusive(v_traceState_7233_)) as u8;
                if v_isSharedCheck_7270_ == 0 {
                    v___x_7248_ = v_traceState_7233_;
                    v_isShared_7249_ = v_isSharedCheck_7270_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_7246_);
                    lean_dec(v_traceState_7233_);
                    v___x_7248_ = lean_box(0);
                    v_isShared_7249_ = v_isSharedCheck_7270_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7250_ = lean_box(0);
                v___x_7251_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__0);
                v___x_7252_ = 0;
                v___x_7253_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__1;
                v___x_7254_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_7254_, 0, v_cls_7219_);
                lean_ctor_set(v___x_7254_, 1, v___x_7250_);
                lean_ctor_set(v___x_7254_, 2, v___x_7253_);
                lean_ctor_set_float(
                    v___x_7254_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_7251_,
                );
                lean_ctor_set_float(
                    v___x_7254_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_7251_,
                );
                lean_ctor_set_uint8(
                    v___x_7254_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_7252_,
                );
                v___x_7255_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___closed__2;
                v___x_7256_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_7256_, 0, v___x_7254_);
                lean_ctor_set(v___x_7256_, 1, v_a_7228_);
                lean_ctor_set(v___x_7256_, 2, v___x_7255_);
                lean_inc(v_ref_7226_);
                v___x_7257_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7257_, 0, v_ref_7226_);
                lean_ctor_set(v___x_7257_, 1, v___x_7256_);
                v___x_7258_ = l_Lean_PersistentArray_push___redArg(v_traces_7246_, v___x_7257_);
                if v_isShared_7249_ == 0 {
                    lean_ctor_set(v___x_7248_, 0, v___x_7258_);
                    v___x_7260_ = v___x_7248_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7269_, 0, v___x_7258_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_7269_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_7245_,
                    );
                    v___x_7260_ = v_reuseFailAlloc_7269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7244_ == 0 {
                    lean_ctor_set(v___x_7243_, 4, v___x_7260_);
                    v___x_7262_ = v___x_7243_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7268_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 0, v_env_7234_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 1, v_nextMacroScope_7235_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 2, v_ngen_7236_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 3, v_auxDeclNGen_7237_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 4, v___x_7260_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 5, v_cache_7238_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 6, v_messages_7239_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 7, v_infoState_7240_);
                    lean_ctor_set(v_reuseFailAlloc_7268_, 8, v_snapshotTasks_7241_);
                    v___x_7262_ = v_reuseFailAlloc_7268_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7263_ = lean_st_ref_set(v___y_7224_, v___x_7262_);
                v___x_7264_ = lean_box(0);
                if v_isShared_7231_ == 0 {
                    lean_ctor_set(v___x_7230_, 0, v___x_7264_);
                    v___x_7266_ = v___x_7230_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7267_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 0, v___x_7264_);
                    v___x_7266_ = v_reuseFailAlloc_7267_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6___boxed(
    mut v_cls_7273_: *mut LeanObject,
    mut v_msg_7274_: *mut LeanObject,
    mut v___y_7275_: *mut LeanObject,
    mut v___y_7276_: *mut LeanObject,
    mut v___y_7277_: *mut LeanObject,
    mut v___y_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7280_: *mut LeanObject = core::ptr::null_mut();
    v_res_7280_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_7273_, v_msg_7274_, v___y_7275_, v___y_7276_, v___y_7277_, v___y_7278_);
    lean_dec(v___y_7278_);
    lean_dec_ref(v___y_7277_);
    lean_dec(v___y_7276_);
    lean_dec_ref(v___y_7275_);
    return v_res_7280_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1()
-> *mut LeanObject {
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
    v___x_7282_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__0;
    v___x_7283_ = l_Lean_stringToMessageData(v___x_7282_);
    return v___x_7283_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4()
-> *mut LeanObject {
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    v___x_7288_ = lean_box(0);
    v___x_7289_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__3;
    v___x_7290_ = l_Lean_mkConst(v___x_7289_, v___x_7288_);
    return v___x_7290_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13()
-> *mut LeanObject {
    let mut v___x_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
    v___x_7306_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10;
    v___x_7307_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__12;
    v___x_7308_ = l_Lean_Name_append(v___x_7307_, v___x_7306_);
    return v___x_7308_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15()
-> *mut LeanObject {
    let mut v___x_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut LeanObject = core::ptr::null_mut();
    v___x_7310_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__14;
    v___x_7311_ = l_Lean_stringToMessageData(v___x_7310_);
    return v___x_7311_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17()
-> *mut LeanObject {
    let mut v___x_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7314_: *mut LeanObject = core::ptr::null_mut();
    v___x_7313_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__16;
    v___x_7314_ = l_Lean_stringToMessageData(v___x_7313_);
    return v___x_7314_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(
    mut v_inductVal_7315_: *mut LeanObject,
    mut v_rel_7316_: *mut LeanObject,
    mut v_a_7317_: *mut LeanObject,
    mut v_a_7318_: *mut LeanObject,
    mut v_a_7319_: *mut LeanObject,
    mut v_a_7320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_7330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7337_: u8 = 0;
    let mut v___x_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univs_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7341_: u8 = 0;
    let mut v___x_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7348_: u8 = 0;
    let mut v_fst_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7353_: u8 = 0;
    let mut v___y_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7380_: u8 = 0;
    let mut v___x_7381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7410_: u8 = 0;
    let mut v___x_7412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7415_: u8 = 0;
    let mut v_a_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7419_: u8 = 0;
    let mut v___x_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7423_: u8 = 0;
    let mut v_reuseFailAlloc_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7429_: u8 = 0;
    let mut v___x_7431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7433_: u8 = 0;
    let mut v_isSharedCheck_7434_: u8 = 0;
    let mut v_unused_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7439_: u8 = 0;
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7443_: u8 = 0;
    let mut v_a_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7447_: u8 = 0;
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7451_: u8 = 0;
    let mut v_a_7452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7455_: u8 = 0;
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7459_: u8 = 0;
    let mut v_options_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7461_: u8 = 0;
    let mut v_inheritedTraceOptions_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: u8 = 0;
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7480_: u8 = 0;
    let mut v___x_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7487_: u8 = 0;
    let mut v_isSharedCheck_7488_: u8 = 0;
    let mut v_a_7489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7492_: u8 = 0;
    let mut v___x_7494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7496_: u8 = 0;
    let mut v_isSharedCheck_7497_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toConstantVal_7329_ = lean_ctor_get(v_inductVal_7315_, 0);
                lean_inc_ref(v_toConstantVal_7329_);
                v_numParams_7330_ = lean_ctor_get(v_inductVal_7315_, 1);
                lean_inc(v_numParams_7330_);
                v_ctors_7331_ = lean_ctor_get(v_inductVal_7315_, 4);
                lean_inc(v_ctors_7331_);
                lean_dec_ref(v_inductVal_7315_);
                v_name_7332_ = lean_ctor_get(v_toConstantVal_7329_, 0);
                v_levelParams_7333_ = lean_ctor_get(v_toConstantVal_7329_, 1);
                v_type_7334_ = lean_ctor_get(v_toConstantVal_7329_, 2);
                v_isSharedCheck_7497_ = (!lean_is_exclusive(v_toConstantVal_7329_)) as u8;
                if v_isSharedCheck_7497_ == 0 {
                    v___x_7336_ = v_toConstantVal_7329_;
                    v_isShared_7337_ = v_isSharedCheck_7497_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_type_7334_);
                    lean_inc(v_levelParams_7333_);
                    lean_inc(v_name_7332_);
                    lean_dec(v_toConstantVal_7329_);
                    v___x_7336_ = lean_box(0);
                    v_isShared_7337_ = v_isSharedCheck_7497_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_7327_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__1);
                v___x_7328_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_7327_, v___y_7323_, v___y_7324_, v___y_7325_, v___y_7326_);
                return v___x_7328_;
            }
            2 => {
                v___x_7338_ = lean_box(0);
                lean_inc(v_levelParams_7333_);
                v_univs_7339_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__2_spec__3(v_levelParams_7333_, v___x_7338_);
                lean_inc(v_ctors_7331_);
                lean_inc(v_numParams_7330_);
                lean_inc(v_name_7332_);
                v___f_7340_ = lean_alloc_closure(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___lam__0___boxed as *mut core::ffi::c_void, 12, 5);
                lean_closure_set(v___f_7340_, 0, v_name_7332_);
                lean_closure_set(v___f_7340_, 1, v_univs_7339_);
                lean_closure_set(v___f_7340_, 2, v_numParams_7330_);
                lean_closure_set(v___f_7340_, 3, v_ctors_7331_);
                lean_closure_set(v___f_7340_, 4, v___x_7338_);
                v___x_7341_ = 0;
                v___x_7342_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__1___redArg(v_type_7334_, v___f_7340_, v___x_7341_, v___x_7341_, v_a_7317_, v_a_7318_, v_a_7319_, v_a_7320_);
                if lean_obj_tag(v___x_7342_) == 0 {
                    v_a_7343_ = lean_ctor_get(v___x_7342_, 0);
                    lean_inc(v_a_7343_);
                    lean_dec_ref_known(v___x_7342_, 1);
                    v_snd_7344_ = lean_ctor_get(v_a_7343_, 1);
                    v_fst_7345_ = lean_ctor_get(v_a_7343_, 0);
                    v_isSharedCheck_7488_ = (!lean_is_exclusive(v_a_7343_)) as u8;
                    if v_isSharedCheck_7488_ == 0 {
                        v___x_7347_ = v_a_7343_;
                        v_isShared_7348_ = v_isSharedCheck_7488_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_7344_);
                        lean_inc(v_fst_7345_);
                        lean_dec(v_a_7343_);
                        v___x_7347_ = lean_box(0);
                        v_isShared_7348_ = v_isSharedCheck_7488_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7336_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    lean_dec(v_ctors_7331_);
                    lean_dec(v_numParams_7330_);
                    lean_dec(v_rel_7316_);
                    v_a_7489_ = lean_ctor_get(v___x_7342_, 0);
                    v_isSharedCheck_7496_ = (!lean_is_exclusive(v___x_7342_)) as u8;
                    if v_isSharedCheck_7496_ == 0 {
                        v___x_7491_ = v___x_7342_;
                        v_isShared_7492_ = v_isSharedCheck_7496_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_7489_);
                        lean_dec(v___x_7342_);
                        v___x_7491_ = lean_box(0);
                        v_isShared_7492_ = v_isSharedCheck_7496_;
                        state = 24;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_7349_ = lean_ctor_get(v_snd_7344_, 0);
                v_snd_7350_ = lean_ctor_get(v_snd_7344_, 1);
                v_isSharedCheck_7487_ = (!lean_is_exclusive(v_snd_7344_)) as u8;
                if v_isSharedCheck_7487_ == 0 {
                    v___x_7352_ = v_snd_7344_;
                    v_isShared_7353_ = v_isSharedCheck_7487_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_7350_);
                    lean_inc(v_fst_7349_);
                    lean_dec(v_snd_7344_);
                    v___x_7352_ = lean_box(0);
                    v_isShared_7353_ = v_isSharedCheck_7487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_options_7460_ = lean_ctor_get(v_a_7319_, 2);
                v_hasTrace_7461_ = lean_ctor_get_uint8(
                    v_options_7460_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_7461_ == 0 {
                    lean_del_object(v___x_7352_);
                    lean_del_object(v___x_7347_);
                    v___y_7355_ = v_a_7317_;
                    v___y_7356_ = v_a_7318_;
                    v___y_7357_ = v_a_7319_;
                    v___y_7358_ = v_a_7320_;
                    state = 5;
                    continue;
                } else {
                    v_inheritedTraceOptions_7462_ = lean_ctor_get(v_a_7319_, 13);
                    v___x_7463_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10;
                    v___x_7479_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
                    v___x_7480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_7462_,
                        v_options_7460_,
                        v___x_7479_,
                    );
                    if v___x_7480_ == 0 {
                        lean_del_object(v___x_7347_);
                        v___y_7465_ = v_a_7317_;
                        v___y_7466_ = v_a_7318_;
                        v___y_7467_ = v_a_7319_;
                        v_options_7468_ = v_options_7460_;
                        v_inheritedTraceOptions_7469_ = v_inheritedTraceOptions_7462_;
                        v___y_7470_ = v_a_7320_;
                        state = 21;
                        continue;
                    } else {
                        v___x_7481_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__17);
                        lean_inc(v_snd_7350_);
                        v___x_7482_ = l_Lean_MessageData_ofExpr(v_snd_7350_);
                        if v_isShared_7348_ == 0 {
                            lean_ctor_set_tag(v___x_7347_, 7);
                            lean_ctor_set(v___x_7347_, 1, v___x_7482_);
                            lean_ctor_set(v___x_7347_, 0, v___x_7481_);
                            v___x_7484_ = v___x_7347_;
                            state = 23;
                            continue;
                        } else {
                            v_reuseFailAlloc_7486_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_7486_, 0, v___x_7481_);
                            lean_ctor_set(v_reuseFailAlloc_7486_, 1, v___x_7482_);
                            v___x_7484_ = v_reuseFailAlloc_7486_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            5 => {
                lean_inc(v_fst_7345_);
                v___x_7359_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7359_, 0, v_fst_7345_);
                v___x_7360_ = 0;
                v___x_7361_ = lean_box(0);
                v___x_7362_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_7359_,
                    v___x_7360_,
                    v___x_7361_,
                    v___y_7355_,
                    v___y_7356_,
                    v___y_7357_,
                    v___y_7358_,
                );
                if lean_obj_tag(v___x_7362_) == 0 {
                    v_a_7363_ = lean_ctor_get(v___x_7362_, 0);
                    lean_inc(v_a_7363_);
                    lean_dec_ref_known(v___x_7362_, 1);
                    v___x_7364_ = l_Lean_Expr_mvarId_x21(v_a_7363_);
                    v___x_7365_ = l_Lean_MVarId_intros(
                        v___x_7364_,
                        v___y_7355_,
                        v___y_7356_,
                        v___y_7357_,
                        v___y_7358_,
                    );
                    if lean_obj_tag(v___x_7365_) == 0 {
                        v_a_7366_ = lean_ctor_get(v___x_7365_, 0);
                        lean_inc(v_a_7366_);
                        lean_dec_ref_known(v___x_7365_, 1);
                        v_fst_7367_ = lean_ctor_get(v_a_7366_, 0);
                        lean_inc(v_fst_7367_);
                        v_snd_7368_ = lean_ctor_get(v_a_7366_, 1);
                        lean_inc(v_snd_7368_);
                        lean_dec(v_a_7366_);
                        v___x_7369_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__4);
                        v___x_7370_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__5;
                        v___x_7371_ = lean_box(0);
                        v___x_7372_ = l_Lean_MVarId_apply(
                            v_snd_7368_,
                            v___x_7369_,
                            v___x_7370_,
                            v___x_7371_,
                            v___y_7355_,
                            v___y_7356_,
                            v___y_7357_,
                            v___y_7358_,
                        );
                        if lean_obj_tag(v___x_7372_) == 0 {
                            v_a_7373_ = lean_ctor_get(v___x_7372_, 0);
                            lean_inc(v_a_7373_);
                            lean_dec_ref_known(v___x_7372_, 1);
                            if lean_obj_tag(v_a_7373_) == 1 {
                                v_tail_7374_ = lean_ctor_get(v_a_7373_, 1);
                                lean_inc(v_tail_7374_);
                                if lean_obj_tag(v_tail_7374_) == 1 {
                                    v_tail_7375_ = lean_ctor_get(v_tail_7374_, 1);
                                    if lean_obj_tag(v_tail_7375_) == 0 {
                                        v_head_7376_ = lean_ctor_get(v_a_7373_, 0);
                                        lean_inc(v_head_7376_);
                                        lean_dec_ref_known(v_a_7373_, 2);
                                        v_head_7377_ = lean_ctor_get(v_tail_7374_, 0);
                                        v_isSharedCheck_7434_ =
                                            (!lean_is_exclusive(v_tail_7374_)) as u8;
                                        if v_isSharedCheck_7434_ == 0 {
                                            v_unused_7435_ = lean_ctor_get(v_tail_7374_, 1);
                                            lean_dec(v_unused_7435_);
                                            v___x_7379_ = v_tail_7374_;
                                            v_isShared_7380_ = v_isSharedCheck_7434_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_inc(v_head_7377_);
                                            lean_dec(v_tail_7374_);
                                            v___x_7379_ = lean_box(0);
                                            v_isShared_7380_ = v_isSharedCheck_7434_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_tail_7374_, 2);
                                        lean_dec_ref_known(v_a_7373_, 2);
                                        lean_dec(v_fst_7367_);
                                        lean_dec(v_a_7363_);
                                        lean_dec(v_snd_7350_);
                                        lean_dec(v_fst_7349_);
                                        lean_dec(v_fst_7345_);
                                        lean_del_object(v___x_7336_);
                                        lean_dec(v_levelParams_7333_);
                                        lean_dec(v_name_7332_);
                                        lean_dec(v_ctors_7331_);
                                        lean_dec(v_numParams_7330_);
                                        lean_dec(v_rel_7316_);
                                        v___y_7323_ = v___y_7355_;
                                        v___y_7324_ = v___y_7356_;
                                        v___y_7325_ = v___y_7357_;
                                        v___y_7326_ = v___y_7358_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_a_7373_, 2);
                                    lean_dec(v_tail_7374_);
                                    lean_dec(v_fst_7367_);
                                    lean_dec(v_a_7363_);
                                    lean_dec(v_snd_7350_);
                                    lean_dec(v_fst_7349_);
                                    lean_dec(v_fst_7345_);
                                    lean_del_object(v___x_7336_);
                                    lean_dec(v_levelParams_7333_);
                                    lean_dec(v_name_7332_);
                                    lean_dec(v_ctors_7331_);
                                    lean_dec(v_numParams_7330_);
                                    lean_dec(v_rel_7316_);
                                    v___y_7323_ = v___y_7355_;
                                    v___y_7324_ = v___y_7356_;
                                    v___y_7325_ = v___y_7357_;
                                    v___y_7326_ = v___y_7358_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_7373_);
                                lean_dec(v_fst_7367_);
                                lean_dec(v_a_7363_);
                                lean_dec(v_snd_7350_);
                                lean_dec(v_fst_7349_);
                                lean_dec(v_fst_7345_);
                                lean_del_object(v___x_7336_);
                                lean_dec(v_levelParams_7333_);
                                lean_dec(v_name_7332_);
                                lean_dec(v_ctors_7331_);
                                lean_dec(v_numParams_7330_);
                                lean_dec(v_rel_7316_);
                                v___y_7323_ = v___y_7355_;
                                v___y_7324_ = v___y_7356_;
                                v___y_7325_ = v___y_7357_;
                                v___y_7326_ = v___y_7358_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_fst_7367_);
                            lean_dec(v_a_7363_);
                            lean_dec(v_snd_7350_);
                            lean_dec(v_fst_7349_);
                            lean_dec(v_fst_7345_);
                            lean_del_object(v___x_7336_);
                            lean_dec(v_levelParams_7333_);
                            lean_dec(v_name_7332_);
                            lean_dec(v_ctors_7331_);
                            lean_dec(v_numParams_7330_);
                            lean_dec(v_rel_7316_);
                            v_a_7436_ = lean_ctor_get(v___x_7372_, 0);
                            v_isSharedCheck_7443_ = (!lean_is_exclusive(v___x_7372_)) as u8;
                            if v_isSharedCheck_7443_ == 0 {
                                v___x_7438_ = v___x_7372_;
                                v_isShared_7439_ = v_isSharedCheck_7443_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_7436_);
                                lean_dec(v___x_7372_);
                                v___x_7438_ = lean_box(0);
                                v_isShared_7439_ = v_isSharedCheck_7443_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_7363_);
                        lean_dec(v_snd_7350_);
                        lean_dec(v_fst_7349_);
                        lean_dec(v_fst_7345_);
                        lean_del_object(v___x_7336_);
                        lean_dec(v_levelParams_7333_);
                        lean_dec(v_name_7332_);
                        lean_dec(v_ctors_7331_);
                        lean_dec(v_numParams_7330_);
                        lean_dec(v_rel_7316_);
                        v_a_7444_ = lean_ctor_get(v___x_7365_, 0);
                        v_isSharedCheck_7451_ = (!lean_is_exclusive(v___x_7365_)) as u8;
                        if v_isSharedCheck_7451_ == 0 {
                            v___x_7446_ = v___x_7365_;
                            v_isShared_7447_ = v_isSharedCheck_7451_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_7444_);
                            lean_dec(v___x_7365_);
                            v___x_7446_ = lean_box(0);
                            v_isShared_7447_ = v_isSharedCheck_7451_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_7350_);
                    lean_dec(v_fst_7349_);
                    lean_dec(v_fst_7345_);
                    lean_del_object(v___x_7336_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    lean_dec(v_ctors_7331_);
                    lean_dec(v_numParams_7330_);
                    lean_dec(v_rel_7316_);
                    v_a_7452_ = lean_ctor_get(v___x_7362_, 0);
                    v_isSharedCheck_7459_ = (!lean_is_exclusive(v___x_7362_)) as u8;
                    if v_isSharedCheck_7459_ == 0 {
                        v___x_7454_ = v___x_7362_;
                        v_isShared_7455_ = v_isSharedCheck_7459_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_7452_);
                        lean_dec(v___x_7362_);
                        v___x_7454_ = lean_box(0);
                        v_isShared_7455_ = v_isSharedCheck_7459_;
                        state = 19;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc(v_fst_7349_);
                v___x_7381_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toCases(
                    v_head_7376_,
                    v_fst_7349_,
                    v___y_7355_,
                    v___y_7356_,
                    v___y_7357_,
                    v___y_7358_,
                );
                if lean_obj_tag(v___x_7381_) == 0 {
                    lean_dec_ref_known(v___x_7381_, 1);
                    v___x_7382_ = l_Lean_Meta_intro1Core(
                        v_head_7377_,
                        v___x_7341_,
                        v___y_7355_,
                        v___y_7356_,
                        v___y_7357_,
                        v___y_7358_,
                    );
                    if lean_obj_tag(v___x_7382_) == 0 {
                        v_a_7383_ = lean_ctor_get(v___x_7382_, 0);
                        lean_inc(v_a_7383_);
                        lean_dec_ref_known(v___x_7382_, 1);
                        v_fst_7384_ = lean_ctor_get(v_a_7383_, 0);
                        lean_inc(v_fst_7384_);
                        v_snd_7385_ = lean_ctor_get(v_a_7383_, 1);
                        lean_inc(v_snd_7385_);
                        lean_dec(v_a_7383_);
                        v___x_7386_ = lean_array_to_list(v_fst_7367_);
                        v___x_7387_ = l_List_mapM_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive_spec__5___lam__0___closed__0;
                        lean_inc(v___x_7386_);
                        v___x_7388_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
                            lean_box(0),
                            v___x_7386_,
                            v___x_7386_,
                            v_numParams_7330_,
                            v___x_7387_,
                        );
                        lean_dec(v___x_7386_);
                        v___x_7389_ = l_List_mapTR_loop___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__2(v___x_7388_, v___x_7338_);
                        v___x_7390_ =
                            l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_toInductive(
                                v_snd_7385_,
                                v_ctors_7331_,
                                v___x_7389_,
                                v_fst_7349_,
                                v_fst_7384_,
                                v___y_7355_,
                                v___y_7356_,
                                v___y_7357_,
                                v___y_7358_,
                            );
                        if lean_obj_tag(v___x_7390_) == 0 {
                            lean_dec_ref_known(v___x_7390_, 1);
                            v___x_7391_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__3___redArg(v_a_7363_, v___y_7356_);
                            v_a_7392_ = lean_ctor_get(v___x_7391_, 0);
                            lean_inc(v_a_7392_);
                            lean_dec_ref(v___x_7391_);
                            lean_inc(v_levelParams_7333_);
                            lean_inc(v_rel_7316_);
                            if v_isShared_7337_ == 0 {
                                lean_ctor_set(v___x_7336_, 2, v_fst_7345_);
                                lean_ctor_set(v___x_7336_, 0, v_rel_7316_);
                                v___x_7394_ = v___x_7336_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_7425_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_7425_, 0, v_rel_7316_);
                                lean_ctor_set(v_reuseFailAlloc_7425_, 1, v_levelParams_7333_);
                                lean_ctor_set(v_reuseFailAlloc_7425_, 2, v_fst_7345_);
                                v___x_7394_ = v_reuseFailAlloc_7425_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7379_);
                            lean_dec(v_a_7363_);
                            lean_dec(v_snd_7350_);
                            lean_dec(v_fst_7345_);
                            lean_del_object(v___x_7336_);
                            lean_dec(v_levelParams_7333_);
                            lean_dec(v_name_7332_);
                            lean_dec(v_rel_7316_);
                            return v___x_7390_;
                        }
                    } else {
                        lean_del_object(v___x_7379_);
                        lean_dec(v_fst_7367_);
                        lean_dec(v_a_7363_);
                        lean_dec(v_snd_7350_);
                        lean_dec(v_fst_7349_);
                        lean_dec(v_fst_7345_);
                        lean_del_object(v___x_7336_);
                        lean_dec(v_levelParams_7333_);
                        lean_dec(v_name_7332_);
                        lean_dec(v_ctors_7331_);
                        lean_dec(v_numParams_7330_);
                        lean_dec(v_rel_7316_);
                        v_a_7426_ = lean_ctor_get(v___x_7382_, 0);
                        v_isSharedCheck_7433_ = (!lean_is_exclusive(v___x_7382_)) as u8;
                        if v_isSharedCheck_7433_ == 0 {
                            v___x_7428_ = v___x_7382_;
                            v_isShared_7429_ = v_isSharedCheck_7433_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_7426_);
                            lean_dec(v___x_7382_);
                            v___x_7428_ = lean_box(0);
                            v_isShared_7429_ = v_isSharedCheck_7433_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_7379_);
                    lean_dec(v_head_7377_);
                    lean_dec(v_fst_7367_);
                    lean_dec(v_a_7363_);
                    lean_dec(v_snd_7350_);
                    lean_dec(v_fst_7349_);
                    lean_dec(v_fst_7345_);
                    lean_del_object(v___x_7336_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    lean_dec(v_ctors_7331_);
                    lean_dec(v_numParams_7330_);
                    lean_dec(v_rel_7316_);
                    return v___x_7381_;
                }
            }
            7 => {
                if v_isShared_7380_ == 0 {
                    lean_ctor_set(v___x_7379_, 1, v___x_7338_);
                    lean_ctor_set(v___x_7379_, 0, v_rel_7316_);
                    v___x_7396_ = v___x_7379_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7424_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7424_, 0, v_rel_7316_);
                    lean_ctor_set(v_reuseFailAlloc_7424_, 1, v___x_7338_);
                    v___x_7396_ = v_reuseFailAlloc_7424_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7397_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_7397_, 0, v___x_7394_);
                lean_ctor_set(v___x_7397_, 1, v_a_7392_);
                lean_ctor_set(v___x_7397_, 2, v___x_7396_);
                v___x_7398_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__4___redArg(v___x_7397_, v___y_7358_);
                v_a_7399_ = lean_ctor_get(v___x_7398_, 0);
                lean_inc(v_a_7399_);
                lean_dec_ref(v___x_7398_);
                v___x_7400_ = l_Lean_addDecl(v_a_7399_, v___x_7341_, v___y_7357_, v___y_7358_);
                if lean_obj_tag(v___x_7400_) == 0 {
                    lean_dec_ref_known(v___x_7400_, 1);
                    lean_inc(v___y_7358_);
                    lean_inc_ref(v___y_7357_);
                    lean_inc(v___y_7356_);
                    lean_inc_ref(v___y_7355_);
                    lean_inc(v_snd_7350_);
                    v___x_7401_ = lean_infer_type(
                        v_snd_7350_,
                        v___y_7355_,
                        v___y_7356_,
                        v___y_7357_,
                        v___y_7358_,
                    );
                    if lean_obj_tag(v___x_7401_) == 0 {
                        v_a_7402_ = lean_ctor_get(v___x_7401_, 0);
                        lean_inc(v_a_7402_);
                        lean_dec_ref_known(v___x_7401_, 1);
                        v___x_7403_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__7;
                        v___x_7404_ = l_Lean_Name_append(v_name_7332_, v___x_7403_);
                        v___x_7405_ = lean_box(0);
                        v___x_7406_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__5___redArg(v___x_7404_, v_levelParams_7333_, v_a_7402_, v_snd_7350_, v___x_7405_, v___y_7358_);
                        v_a_7407_ = lean_ctor_get(v___x_7406_, 0);
                        v_isSharedCheck_7415_ = (!lean_is_exclusive(v___x_7406_)) as u8;
                        if v_isSharedCheck_7415_ == 0 {
                            v___x_7409_ = v___x_7406_;
                            v_isShared_7410_ = v_isSharedCheck_7415_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7407_);
                            lean_dec(v___x_7406_);
                            v___x_7409_ = lean_box(0);
                            v_isShared_7410_ = v_isSharedCheck_7415_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_7350_);
                        lean_dec(v_levelParams_7333_);
                        lean_dec(v_name_7332_);
                        v_a_7416_ = lean_ctor_get(v___x_7401_, 0);
                        v_isSharedCheck_7423_ = (!lean_is_exclusive(v___x_7401_)) as u8;
                        if v_isSharedCheck_7423_ == 0 {
                            v___x_7418_ = v___x_7401_;
                            v_isShared_7419_ = v_isSharedCheck_7423_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_7416_);
                            lean_dec(v___x_7401_);
                            v___x_7418_ = lean_box(0);
                            v_isShared_7419_ = v_isSharedCheck_7423_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_7350_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    return v___x_7400_;
                }
            }
            9 => {
                if v_isShared_7410_ == 0 {
                    lean_ctor_set_tag(v___x_7409_, 1);
                    v___x_7412_ = v___x_7409_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7414_, 0, v_a_7407_);
                    v___x_7412_ = v_reuseFailAlloc_7414_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_7413_ = l_Lean_addDecl(v___x_7412_, v___x_7341_, v___y_7357_, v___y_7358_);
                return v___x_7413_;
            }
            11 => {
                if v_isShared_7419_ == 0 {
                    v___x_7421_ = v___x_7418_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7422_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7422_, 0, v_a_7416_);
                    v___x_7421_ = v_reuseFailAlloc_7422_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7421_;
            }
            13 => {
                if v_isShared_7429_ == 0 {
                    v___x_7431_ = v___x_7428_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7432_, 0, v_a_7426_);
                    v___x_7431_ = v_reuseFailAlloc_7432_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7431_;
            }
            15 => {
                if v_isShared_7439_ == 0 {
                    v___x_7441_ = v___x_7438_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7442_, 0, v_a_7436_);
                    v___x_7441_ = v_reuseFailAlloc_7442_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7441_;
            }
            17 => {
                if v_isShared_7447_ == 0 {
                    v___x_7449_ = v___x_7446_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7450_, 0, v_a_7444_);
                    v___x_7449_ = v_reuseFailAlloc_7450_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7449_;
            }
            19 => {
                if v_isShared_7455_ == 0 {
                    v___x_7457_ = v___x_7454_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7458_, 0, v_a_7452_);
                    v___x_7457_ = v_reuseFailAlloc_7458_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7457_;
            }
            21 => {
                v___x_7471_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
                v___x_7472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_7469_,
                    v_options_7468_,
                    v___x_7471_,
                );
                if v___x_7472_ == 0 {
                    lean_del_object(v___x_7352_);
                    v___y_7355_ = v___y_7465_;
                    v___y_7356_ = v___y_7466_;
                    v___y_7357_ = v___y_7467_;
                    v___y_7358_ = v___y_7470_;
                    state = 5;
                    continue;
                } else {
                    v___x_7473_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__15);
                    lean_inc(v_fst_7345_);
                    v___x_7474_ = l_Lean_MessageData_ofExpr(v_fst_7345_);
                    if v_isShared_7353_ == 0 {
                        lean_ctor_set_tag(v___x_7352_, 7);
                        lean_ctor_set(v___x_7352_, 1, v___x_7474_);
                        lean_ctor_set(v___x_7352_, 0, v___x_7473_);
                        v___x_7476_ = v___x_7352_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_7478_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7478_, 0, v___x_7473_);
                        lean_ctor_set(v_reuseFailAlloc_7478_, 1, v___x_7474_);
                        v___x_7476_ = v_reuseFailAlloc_7478_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                v___x_7477_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_7463_, v___x_7476_, v___y_7465_, v___y_7466_, v___y_7467_, v___y_7470_);
                if lean_obj_tag(v___x_7477_) == 0 {
                    lean_dec_ref_known(v___x_7477_, 1);
                    v___y_7355_ = v___y_7465_;
                    v___y_7356_ = v___y_7466_;
                    v___y_7357_ = v___y_7467_;
                    v___y_7358_ = v___y_7470_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v_snd_7350_);
                    lean_dec(v_fst_7349_);
                    lean_dec(v_fst_7345_);
                    lean_del_object(v___x_7336_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    lean_dec(v_ctors_7331_);
                    lean_dec(v_numParams_7330_);
                    lean_dec(v_rel_7316_);
                    return v___x_7477_;
                }
            }
            23 => {
                v___x_7485_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v___x_7463_, v___x_7484_, v_a_7317_, v_a_7318_, v_a_7319_, v_a_7320_);
                if lean_obj_tag(v___x_7485_) == 0 {
                    lean_dec_ref_known(v___x_7485_, 1);
                    v___y_7465_ = v_a_7317_;
                    v___y_7466_ = v_a_7318_;
                    v___y_7467_ = v_a_7319_;
                    v_options_7468_ = v_options_7460_;
                    v_inheritedTraceOptions_7469_ = v_inheritedTraceOptions_7462_;
                    v___y_7470_ = v_a_7320_;
                    state = 21;
                    continue;
                } else {
                    lean_del_object(v___x_7352_);
                    lean_dec(v_snd_7350_);
                    lean_dec(v_fst_7349_);
                    lean_dec(v_fst_7345_);
                    lean_del_object(v___x_7336_);
                    lean_dec(v_levelParams_7333_);
                    lean_dec(v_name_7332_);
                    lean_dec(v_ctors_7331_);
                    lean_dec(v_numParams_7330_);
                    lean_dec(v_rel_7316_);
                    return v___x_7485_;
                }
            }
            24 => {
                if v_isShared_7492_ == 0 {
                    v___x_7494_ = v___x_7491_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7495_, 0, v_a_7489_);
                    v___x_7494_ = v_reuseFailAlloc_7495_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___boxed(
    mut v_inductVal_7498_: *mut LeanObject,
    mut v_rel_7499_: *mut LeanObject,
    mut v_a_7500_: *mut LeanObject,
    mut v_a_7501_: *mut LeanObject,
    mut v_a_7502_: *mut LeanObject,
    mut v_a_7503_: *mut LeanObject,
    mut v_a_7504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7505_: *mut LeanObject = core::ptr::null_mut();
    v_res_7505_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(
        v_inductVal_7498_,
        v_rel_7499_,
        v_a_7500_,
        v_a_7501_,
        v_a_7502_,
        v_a_7503_,
    );
    lean_dec(v_a_7503_);
    lean_dec_ref(v_a_7502_);
    lean_dec(v_a_7501_);
    lean_dec_ref(v_a_7500_);
    return v_res_7505_;
}
pub unsafe fn _init_l_Lean_Meta_mkSumOfProducts___closed__3() -> *mut LeanObject {
    let mut v___x_7510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    v___x_7510_ = l_Lean_Meta_mkSumOfProducts___closed__2;
    v___x_7511_ = l_Lean_stringToMessageData(v___x_7510_);
    return v___x_7511_;
}
pub unsafe fn _init_l_Lean_Meta_mkSumOfProducts___closed__5() -> *mut LeanObject {
    let mut v___x_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7514_: *mut LeanObject = core::ptr::null_mut();
    v___x_7513_ = l_Lean_Meta_mkSumOfProducts___closed__4;
    v___x_7514_ = l_Lean_stringToMessageData(v___x_7513_);
    return v___x_7514_;
}
pub unsafe fn l_Lean_Meta_mkSumOfProducts(
    mut v_declName_7515_: *mut LeanObject,
    mut v_a_7516_: *mut LeanObject,
    mut v_a_7517_: *mut LeanObject,
    mut v_a_7518_: *mut LeanObject,
    mut v_a_7519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7537_: u8 = 0;
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7541_: u8 = 0;
    let mut v_options_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7543_: u8 = 0;
    let mut v_inheritedTraceOptions_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: u8 = 0;
    let mut v___x_7548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7542_ = lean_ctor_get(v_a_7518_, 2);
                v_hasTrace_7543_ = lean_ctor_get_uint8(
                    v_options_7542_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_7543_ == 0 {
                    v___y_7522_ = v_a_7516_;
                    v___y_7523_ = v_a_7517_;
                    v___y_7524_ = v_a_7518_;
                    v___y_7525_ = v_a_7519_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_7544_ = lean_ctor_get(v_a_7518_, 13);
                    v_cls_7545_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10;
                    v___x_7546_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13_once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__13);
                    v___x_7547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_7544_,
                        v_options_7542_,
                        v___x_7546_,
                    );
                    if v___x_7547_ == 0 {
                        v___y_7522_ = v_a_7516_;
                        v___y_7523_ = v_a_7517_;
                        v___y_7524_ = v_a_7518_;
                        v___y_7525_ = v_a_7519_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7548_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSumOfProducts___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSumOfProducts___closed__5_once),
                            _init_l_Lean_Meta_mkSumOfProducts___closed__5,
                        );
                        lean_inc(v_declName_7515_);
                        v___x_7549_ = l_Lean_MessageData_ofName(v_declName_7515_);
                        v___x_7550_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7550_, 0, v___x_7548_);
                        lean_ctor_set(v___x_7550_, 1, v___x_7549_);
                        v___x_7551_ = l_Lean_addTrace___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl_spec__6(v_cls_7545_, v___x_7550_, v_a_7516_, v_a_7517_, v_a_7518_, v_a_7519_);
                        if lean_obj_tag(v___x_7551_) == 0 {
                            lean_dec_ref_known(v___x_7551_, 1);
                            v___y_7522_ = v_a_7516_;
                            v___y_7523_ = v_a_7517_;
                            v___y_7524_ = v_a_7518_;
                            v___y_7525_ = v_a_7519_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_declName_7515_);
                            return v___x_7551_;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_declName_7515_);
                v___x_7526_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_constrToProp_spec__0(v_declName_7515_, v___y_7522_, v___y_7523_, v___y_7524_, v___y_7525_);
                if lean_obj_tag(v___x_7526_) == 0 {
                    v_a_7527_ = lean_ctor_get(v___x_7526_, 0);
                    lean_inc(v_a_7527_);
                    lean_dec_ref_known(v___x_7526_, 1);
                    if lean_obj_tag(v_a_7527_) == 5 {
                        v_val_7528_ = lean_ctor_get(v_a_7527_, 0);
                        lean_inc_ref(v_val_7528_);
                        lean_dec_ref_known(v_a_7527_, 1);
                        v___x_7529_ = l_Lean_Meta_mkSumOfProducts___closed__1;
                        v___x_7530_ = l_Lean_Name_append(v_declName_7515_, v___x_7529_);
                        v___x_7531_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl(v_val_7528_, v___x_7530_, v___y_7522_, v___y_7523_, v___y_7524_, v___y_7525_);
                        return v___x_7531_;
                    } else {
                        lean_dec(v_a_7527_);
                        lean_dec(v_declName_7515_);
                        v___x_7532_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSumOfProducts___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_mkSumOfProducts___closed__3_once),
                            _init_l_Lean_Meta_mkSumOfProducts___closed__3,
                        );
                        v___x_7533_ = l_Lean_throwError___at___00__private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_MVarId_existsi_spec__0___redArg(v___x_7532_, v___y_7522_, v___y_7523_, v___y_7524_, v___y_7525_);
                        return v___x_7533_;
                    }
                } else {
                    lean_dec(v_declName_7515_);
                    v_a_7534_ = lean_ctor_get(v___x_7526_, 0);
                    v_isSharedCheck_7541_ = (!lean_is_exclusive(v___x_7526_)) as u8;
                    if v_isSharedCheck_7541_ == 0 {
                        v___x_7536_ = v___x_7526_;
                        v_isShared_7537_ = v_isSharedCheck_7541_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7534_);
                        lean_dec(v___x_7526_);
                        v___x_7536_ = lean_box(0);
                        v_isShared_7537_ = v_isSharedCheck_7541_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7537_ == 0 {
                    v___x_7539_ = v___x_7536_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7540_, 0, v_a_7534_);
                    v___x_7539_ = v_reuseFailAlloc_7540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkSumOfProducts___boxed(
    mut v_declName_7552_: *mut LeanObject,
    mut v_a_7553_: *mut LeanObject,
    mut v_a_7554_: *mut LeanObject,
    mut v_a_7555_: *mut LeanObject,
    mut v_a_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7558_: *mut LeanObject = core::ptr::null_mut();
    v_res_7558_ =
        l_Lean_Meta_mkSumOfProducts(v_declName_7552_, v_a_7553_, v_a_7554_, v_a_7555_, v_a_7556_);
    lean_dec(v_a_7556_);
    lean_dec_ref(v_a_7555_);
    lean_dec(v_a_7554_);
    lean_dec_ref(v_a_7553_);
    return v_res_7558_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    v___x_7598_ = lean_unsigned_to_nat(3649998058);
    v___x_7599_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
    v___x_7600_ = l_Lean_Name_num___override(v___x_7599_, v___x_7598_);
    return v___x_7600_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    v___x_7602_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
    v___x_7603_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
    v___x_7604_ = l_Lean_Name_str___override(v___x_7603_, v___x_7602_);
    return v___x_7604_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    v___x_7606_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_;
    v___x_7607_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
    v___x_7608_ = l_Lean_Name_str___override(v___x_7607_, v___x_7606_);
    return v___x_7608_;
}
pub unsafe fn _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7611_: *mut LeanObject = core::ptr::null_mut();
    v___x_7609_ = lean_unsigned_to_nat(2);
    v___x_7610_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
    v___x_7611_ = l_Lean_Name_num___override(v___x_7610_, v___x_7609_);
    return v___x_7611_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_7613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7614_: u8 = 0;
    let mut v___x_7615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut LeanObject = core::ptr::null_mut();
    v___x_7613_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_mkIffOfInductivePropImpl___closed__10;
    v___x_7614_ = 0;
    v___x_7615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_);
    v___x_7616_ = l_Lean_registerTraceClass(v___x_7613_, v___x_7614_, v___x_7615_);
    return v___x_7616_;
}
pub unsafe fn l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2____boxed(
    mut v_a_7617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7618_: *mut LeanObject = core::ptr::null_mut();
    v_res_7618_ = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
    return v_res_7618_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MkIffOfInductiveProp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_MkIffOfInductiveProp_0__Lean_Meta_initFn_00___x40_Lean_Meta_MkIffOfInductiveProp_3649998058____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MkIffOfInductiveProp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MkIffOfInductiveProp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_MkIffOfInductiveProp(builtin);
}
