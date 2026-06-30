// Lean compiler output
// Module: Lean.Elab.BuiltinDo.For
// Imports: Lean.Elab.BuiltinDo.Basic Lean.Parser.Do Init.Control.Do Lean.Meta.ProdN
use crate::ffi::{
    lean_array_fget, lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget, lean_array_uget_borrowed,
    lean_array_uset, lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_isNone, l_Lean_TSyntax_getId,
    l_Lean_mkIdentFrom,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray2___redArg, l_Lean_Macro_throwErrorAt___redArg,
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isIdent, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node7, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_Pi_instInhabited___redArg___lam__0, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_instMonad___redArg, l_String_toRawSubstring_x27, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_mkFreshUserName,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Elab::Binders::l_Lean_Elab_Term_addLocalVarInfo;
use crate::r#gen::Lean::Elab::BuiltinDo::Basic::{
    initialize_Lean_Elab_BuiltinDo_Basic, runtime_initialize_Lean_Elab_BuiltinDo_Basic,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    l_Lean_Elab_Do_DoElemCont_continueWithUnit, l_Lean_Elab_Do_DoElemCont_ensureUnitAt,
    l_Lean_Elab_Do_bindMutVarsFromTuple, l_Lean_Elab_Do_checkMutVarsForShadowing,
    l_Lean_Elab_Do_doElemElabAttribute, l_Lean_Elab_Do_elabDoSeq___boxed,
    l_Lean_Elab_Do_enterLoopBody___redArg, l_Lean_Elab_Do_getReturnCont___redArg,
    l_Lean_Elab_Do_mkBindApp, l_Lean_Elab_Do_mkMonadApp, l_Lean_Elab_Do_mkPureApp,
};
use crate::r#gen::Lean::Elab::Do::InferControlInfo::l_Lean_Elab_Do_inferControlInfoSeq;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_addTermInfo_x27, l_Lean_Elab_Term_elabTermEnsuringType,
    l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed,
    l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, l_Lean_Elab_Term_mkInstMVar,
};
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_getBetterRef, l_Lean_Elab_macroAttribute, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_fvarId_x21, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkApp7, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkLambda, l_Lean_mkSimpleThunk, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_toExpr, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkAppM, l_Lean_Meta_mkNone, l_Lean_Meta_mkSome,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_getFVarFromUserName,
    l_Lean_Meta_getLocalDeclFromUserName, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_isLevelDefEq,
    l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkFreshLevelMVar, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_getDecLevel;
use crate::r#gen::Lean::Meta::ProdN::{
    initialize_Lean_Meta_ProdN, l_Lean_Meta_mkProdMkN, runtime_initialize_Lean_Meta_ProdN,
};
use crate::r#gen::Lean::Parser::Do::{
    initialize_Lean_Parser_Do, runtime_initialize_Lean_Parser_Do,
};
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__0_value) as *mut leanh::LeanObject,13655884332201764339 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 112, 112, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [83, 116, 100, 46, 116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut leanh::LeanObject,13215525487457488549 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [84, 111, 83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__8_value) as *mut leanh::LeanObject,7754083906429771139 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__6_value) as *mut leanh::LeanObject,13029182796945285130 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__9_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__10_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__12_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [95, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 95, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__16_value) as *mut leanh::LeanObject,16096857990383608286 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 83, 101, 113, 73, 116, 101, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 111, 76, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 101, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 116, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 101, 116, 73, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 61, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 111, 83, 101, 113, 73, 110, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 77, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 116, 100, 46, 83, 116, 114, 101, 97, 109, 46, 110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 116, 114, 101, 97, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [110, 101, 120, 116, 63, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__5_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__34_value) as *mut leanh::LeanObject,17138251589876785539 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__35_value) as *mut leanh::LeanObject,3899314177519732191 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__37_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [119, 105, 116, 104, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut leanh::LeanObject,17416048715816169289 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [79, 112, 116, 105, 111, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut leanh::LeanObject,18184376426117065311 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43_value) as *mut leanh::LeanObject,9480010471355609749 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__47_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__48_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 111, 66, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [98, 114, 101, 97, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 111, 109, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut leanh::LeanObject,15308379890181982757 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__46_value) as *mut leanh::LeanObject,18184376426117065311 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53_value) as *mut leanh::LeanObject,4893146552088433753 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__56_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__57_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 117, 112, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__62_value) as *mut leanh::LeanObject,9871775667037945883 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [115, 39, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69_value) as *mut leanh::LeanObject,6632439502835183307 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 111, 82, 101, 97, 115, 115, 105, 103, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [108, 101, 116, 73, 100, 68, 101, 99, 108, 78, 111, 66, 105, 110, 100, 101, 114, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [100, 111, 78, 101, 115, 116, 101, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [100, 111, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value: leanh::LeanStringObject<56> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [84, 104, 101, 32, 112, 114, 111, 111, 102, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 104, 101, 114, 101, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 46, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 111, 70, 111, 114, 68, 101, 99, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject,9513652089846993813 as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 111, 70, 111, 114, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__0_value)
                as *mut leanh::LeanObject,
            16953626593407929508 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [105, 110, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75_value) as *mut leanh::LeanObject,4570674678924417756 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28_value) as *mut leanh::LeanObject,3326968124746134365 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18_value) as *mut leanh::LeanObject,940684074193935882 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__6_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [102, 111, 114, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__7_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [58, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__8_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__9_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14_value) as *mut leanh::LeanObject,3984140175429830279 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29_value) as *mut leanh::LeanObject,4365236509002904093 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31_value) as *mut leanh::LeanObject,9383794970646754147 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40_value) as *mut leanh::LeanObject,13242179749370575553 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__13_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Do_expandDoFor___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41_value) as *mut leanh::LeanObject,16529391333736644786 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_expandDoFor___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__15_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 100, 101, 110, 116, 0],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_expandDoFor___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__15_value)
                as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_expandDoFor___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_expandDoFor___closed__16_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 112, 97, 110, 100, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__0_value) as *mut leanh::LeanObject,18312965975140834652 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [85, 110, 105, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__0_value)
                as *mut leanh::LeanObject,
            9833841078580172006 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__1_value)
                as *mut leanh::LeanObject,
            565778312915565143 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value: leanh::LeanStringObject<44> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            32, 98, 117, 116, 32, 116, 104, 101, 32, 105, 110, 102, 111, 32, 115, 97, 105, 100, 32,
            116, 104, 101, 114, 101, 32, 105, 115, 32, 110, 111, 32, 101, 97, 114, 108, 121, 32,
            114, 101, 116, 117, 114, 110, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            69, 97, 114, 108, 121, 32, 114, 101, 116, 117, 114, 110, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            60, 110, 111, 116, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 62, 0,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__3___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 111, 110, 101, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [121, 105, 101, 108, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [70, 111, 114, 73, 110, 83, 116, 101, 112, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__0_value)
                as *mut leanh::LeanObject,
            8016886460890159001 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__8___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__8___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [114, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__0_value)
                as *mut leanh::LeanObject,
            2981963283782553289 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15_value) as *mut leanh::LeanObject,13286986945483979944 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [66, 114, 101, 97, 107, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [114, 117, 110, 75, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [109, 97, 116, 99, 104, 95, 49, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__3_value)
                as *mut leanh::LeanObject,
            10906666425700568089 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__4_value)
                as *mut leanh::LeanObject,
            2052082663577137876 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__5_value)
                as *mut leanh::LeanObject,
            12942615993048023751 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [80, 114, 111, 100, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [102, 115, 116, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__7_value)
                as *mut leanh::LeanObject,
            15289851429949568889 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__8_value)
                as *mut leanh::LeanObject,
            8286241746160725162 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__10___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__10___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [77, 101, 109, 98, 101, 114, 115, 104, 105, 112, 0],
};
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [109, 101, 109, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
                as *mut leanh::LeanObject,
            7877420268164864461 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__1_value)
                as *mut leanh::LeanObject,
            5015202941514963680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___lam__12___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__2_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 111, 114, 73, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
                as *mut leanh::LeanObject,
            11398022837381273823 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 111, 114, 73, 110, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__0_value)
                as *mut leanh::LeanObject,
            11398022837381273823 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__2_value)
                as *mut leanh::LeanObject,
            6704322920896662537 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___lam__12___closed__0_value)
                as *mut leanh::LeanObject,
            7877420268164864461 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__5_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [100, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__5_value)
                as *mut leanh::LeanObject,
            16646031496814324272 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__7_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [70, 111, 114, 73, 110, 39, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__8_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
                as *mut leanh::LeanObject,
            8702119947958352715 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__9_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [102, 111, 114, 73, 110, 39, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__7_value)
                as *mut leanh::LeanObject,
            8702119947958352715 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Do_elabDoFor___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__9_value)
                as *mut leanh::LeanObject,
            6740408439742725642 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__11_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [206, 177, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__11_value)
                as *mut leanh::LeanObject,
            988715873908496486 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__13_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 1,
        m_data: [207, 129, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__13_value)
                as *mut leanh::LeanObject,
            17734088147927324564 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__15_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [95, 95, 114, 0],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Do_elabDoFor___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__15_value)
                as *mut leanh::LeanObject,
            6333055220850301478 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Do_elabDoFor___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Do_elabDoFor___closed__16_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 68, 111, 70, 111, 114, 0]};
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67_value) as *mut leanh::LeanObject,102172329646148436 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__0_value) as *mut leanh::LeanObject,13250242672952379177 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_macroScope_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3331_: u8 = 0;
    let mut v_quotContext_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_macroScope_3326_ = leanh::lean_ctor_get(v___y_3325_, 0);
                v_traceMsgs_3327_ = leanh::lean_ctor_get(v___y_3325_, 1);
                v_expandedMacroDecls_3328_ = leanh::lean_ctor_get(v___y_3325_, 2);
                v_isSharedCheck_3341_ = (!leanh::lean_is_exclusive(v___y_3325_)) as u8;
                if v_isSharedCheck_3341_ == 0 {
                    v___x_3330_ = v___y_3325_;
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expandedMacroDecls_3328_);
                    leanh::lean_inc(v_traceMsgs_3327_);
                    leanh::lean_inc(v_macroScope_3326_);
                    leanh::lean_dec(v___y_3325_);
                    v___x_3330_ = leanh::lean_box(0);
                    v_isShared_3331_ = v_isSharedCheck_3341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_3332_ = leanh::lean_ctor_get(v___y_3324_, 1);
                v___x_3333_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___closed__1;
                v___x_3334_ = leanh::lean_unsigned_to_nat(1);
                v___x_3335_ = lean_nat_add(v_macroScope_3326_, v___x_3334_);
                if v_isShared_3331_ == 0 {
                    leanh::lean_ctor_set(v___x_3330_, 0, v___x_3335_);
                    v___x_3337_ = v___x_3330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_traceMsgs_3327_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3340_,
                        2,
                        v_expandedMacroDecls_3328_,
                    );
                    v___x_3337_ = v_reuseFailAlloc_3340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_quotContext_3332_);
                v___x_3338_ =
                    l_Lean_addMacroScope(v_quotContext_3332_, v___x_3333_, v_macroScope_3326_);
                v___x_3339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3339_, 0, v___x_3338_);
                leanh::lean_ctor_set(v___x_3339_, 1, v___x_3337_);
                return v___x_3339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1___boxed(
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3344_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3342_, v___y_3343_);
    leanh::lean_dec_ref(v___y_3342_);
    return v_res_3344_;
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
    mut v_ref_3345_: *mut leanh::LeanObject,
    mut v_canonical_3346_: u8,
    mut v___y_3347_: *mut leanh::LeanObject,
    mut v___y_3348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3349_ = l_Lean_Elab_Term_mkFreshBinderName___at___00Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1_spec__1(v___y_3347_, v___y_3348_);
                v_a_3350_ = leanh::lean_ctor_get(v___x_3349_, 0);
                v_a_3351_ = leanh::lean_ctor_get(v___x_3349_, 1);
                v_isSharedCheck_3359_ = (!leanh::lean_is_exclusive(v___x_3349_)) as u8;
                if v_isSharedCheck_3359_ == 0 {
                    v___x_3353_ = v___x_3349_;
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3351_);
                    leanh::lean_inc(v_a_3350_);
                    leanh::lean_dec(v___x_3349_);
                    v___x_3353_ = leanh::lean_box(0);
                    v_isShared_3354_ = v_isSharedCheck_3359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3355_ = l_Lean_mkIdentFrom(v_ref_3345_, v_a_3350_, v_canonical_3346_);
                if v_isShared_3354_ == 0 {
                    leanh::lean_ctor_set(v___x_3353_, 0, v___x_3355_);
                    v___x_3357_ = v___x_3353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 0, v___x_3355_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_a_3351_);
                    v___x_3357_ = v_reuseFailAlloc_3358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1___boxed(
    mut v_ref_3360_: *mut leanh::LeanObject,
    mut v_canonical_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonical_boxed_3364_: u8 = 0;
    let mut v_res_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3364_ = (leanh::lean_unbox(v_canonical_3361_) as u8);
    v_res_3365_ = l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
        v_ref_3360_,
        v_canonical_boxed_3364_,
        v___y_3362_,
        v___y_3363_,
    );
    leanh::lean_dec_ref(v___y_3362_);
    leanh::lean_dec(v_ref_3360_);
    return v_res_3365_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3370_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__3;
    v___x_3371_ = l_String_toRawSubstring_x27(v___x_3370_);
    return v___x_3371_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_3401_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3411_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__32;
    v___x_3412_ = l_String_toRawSubstring_x27(v___x_3411_);
    return v___x_3412_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44()
-> *mut leanh::LeanObject {
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__43;
    v___x_3431_ = l_String_toRawSubstring_x27(v___x_3430_);
    return v___x_3431_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54()
-> *mut leanh::LeanObject {
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__53;
    v___x_3449_ = l_String_toRawSubstring_x27(v___x_3448_);
    return v___x_3449_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65()
-> *mut leanh::LeanObject {
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__64;
    v___x_3469_ = l_String_toRawSubstring_x27(v___x_3468_);
    return v___x_3469_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70()
-> *mut leanh::LeanObject {
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__69;
    v___x_3475_ = l_String_toRawSubstring_x27(v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(
    mut v___x_3484_: *mut leanh::LeanObject,
    mut v___x_3485_: *mut leanh::LeanObject,
    mut v___x_3486_: *mut leanh::LeanObject,
    mut v___x_3487_: u8,
    mut v___x_3488_: *mut leanh::LeanObject,
    mut v___x_3489_: *mut leanh::LeanObject,
    mut v___x_3490_: *mut leanh::LeanObject,
    mut v___f_3491_: *mut leanh::LeanObject,
    mut v_fst_3492_: *mut leanh::LeanObject,
    mut v___x_3493_: *mut leanh::LeanObject,
    mut v_snd_3494_: *mut leanh::LeanObject,
    mut v_x_3495_: *mut leanh::LeanObject,
    mut v_h_x3f_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
    mut v___y_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_a_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_reuseFailAlloc_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v_val_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3728_: u8 = 0;
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3732_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3499_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3485_);
                v___x_3500_ = l_Lean_Syntax_getArg(v___x_3484_, v___x_3486_);
                if leanh::lean_obj_tag(v_h_x3f_3496_) == 1 {
                    v_val_3720_ = leanh::lean_ctor_get(v_h_x3f_3496_, 0);
                    v___x_3721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__77;
                    v___x_3722_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_val_3720_,
                        v___x_3721_,
                        v___y_3497_,
                        v___y_3498_,
                    );
                    if leanh::lean_obj_tag(v___x_3722_) == 0 {
                        v_a_3723_ = leanh::lean_ctor_get(v___x_3722_, 1);
                        leanh::lean_inc(v_a_3723_);
                        leanh::lean_dec_ref_known(v___x_3722_, 2);
                        v___y_3502_ = v_a_3723_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3500_);
                        leanh::lean_dec(v___x_3499_);
                        leanh::lean_dec(v_snd_3494_);
                        leanh::lean_dec_ref(v___x_3493_);
                        leanh::lean_dec(v_fst_3492_);
                        leanh::lean_dec_ref(v___f_3491_);
                        leanh::lean_dec_ref(v___x_3490_);
                        leanh::lean_dec_ref(v___x_3489_);
                        leanh::lean_dec_ref(v___x_3488_);
                        v_a_3724_ = leanh::lean_ctor_get(v___x_3722_, 0);
                        v_a_3725_ = leanh::lean_ctor_get(v___x_3722_, 1);
                        v_isSharedCheck_3732_ =
                            (!leanh::lean_is_exclusive(v___x_3722_)) as u8;
                        if v_isSharedCheck_3732_ == 0 {
                            v___x_3727_ = v___x_3722_;
                            v_isShared_3728_ = v_isSharedCheck_3732_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3725_);
                            leanh::lean_inc(v_a_3724_);
                            leanh::lean_dec(v___x_3722_);
                            v___x_3727_ = leanh::lean_box(0);
                            v_isShared_3728_ = v_isSharedCheck_3732_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___y_3502_ = v___y_3498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_quotContext_3503_ = leanh::lean_ctor_get(v___y_3497_, 1);
                v_currMacroScope_3504_ = leanh::lean_ctor_get(v___y_3497_, 2);
                v_ref_3505_ = leanh::lean_ctor_get(v___y_3497_, 5);
                v_ref_3506_ = l_Lean_replaceRef(v___x_3500_, v_ref_3505_);
                v___x_3507_ = l_Lean_SourceInfo_fromRef(v_ref_3506_, v___x_3487_);
                leanh::lean_dec(v_ref_3506_);
                v___x_3508_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__0;
                leanh::lean_inc_ref_n(v___x_3490_, 3);
                leanh::lean_inc_ref_n(v___x_3489_, 3);
                leanh::lean_inc_ref_n(v___x_3488_, 3);
                v___x_3509_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3508_);
                v___x_3510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__1;
                v___x_3511_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3510_);
                v___x_3512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__2;
                leanh::lean_inc_n(v___x_3507_, 6);
                v___x_3513_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3513_, 0, v___x_3507_);
                leanh::lean_ctor_set(v___x_3513_, 1, v___x_3512_);
                v___x_3514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__4);
                v___x_3515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__7;
                leanh::lean_inc(v_currMacroScope_3504_);
                leanh::lean_inc(v_quotContext_3503_);
                v___x_3516_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3515_, v_currMacroScope_3504_);
                v___x_3517_ = leanh::lean_box(0);
                v___x_3518_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__11;
                v___x_3519_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3519_, 0, v___x_3507_);
                leanh::lean_ctor_set(v___x_3519_, 1, v___x_3514_);
                leanh::lean_ctor_set(v___x_3519_, 2, v___x_3516_);
                leanh::lean_ctor_set(v___x_3519_, 3, v___x_3518_);
                leanh::lean_inc(v___x_3511_);
                v___x_3520_ =
                    l_Lean_Syntax_node2(v___x_3507_, v___x_3511_, v___x_3513_, v___x_3519_);
                v___x_3521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_3522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__14;
                v___x_3523_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3522_);
                v___x_3524_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__15;
                v___x_3525_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3525_, 0, v___x_3507_);
                leanh::lean_ctor_set(v___x_3525_, 1, v___x_3524_);
                leanh::lean_inc(v___x_3523_);
                v___x_3526_ = l_Lean_Syntax_node1(v___x_3507_, v___x_3523_, v___x_3525_);
                leanh::lean_inc(v___x_3500_);
                leanh::lean_inc_n(v___x_3526_, 2);
                v___x_3527_ = l_Lean_Syntax_node4(
                    v___x_3507_,
                    v___x_3521_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3526_,
                    v___x_3500_,
                );
                v_macroScope_3528_ = leanh::lean_ctor_get(v___y_3502_, 0);
                v_traceMsgs_3529_ = leanh::lean_ctor_get(v___y_3502_, 1);
                v_expandedMacroDecls_3530_ = leanh::lean_ctor_get(v___y_3502_, 2);
                v_isSharedCheck_3719_ = (!leanh::lean_is_exclusive(v___y_3502_)) as u8;
                if v_isSharedCheck_3719_ == 0 {
                    v___x_3532_ = v___y_3502_;
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_expandedMacroDecls_3530_);
                    leanh::lean_inc(v_traceMsgs_3529_);
                    leanh::lean_inc(v_macroScope_3528_);
                    leanh::lean_dec(v___y_3502_);
                    v___x_3532_ = leanh::lean_box(0);
                    v_isShared_3533_ = v_isSharedCheck_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3534_ = lean_nat_add(v_macroScope_3528_, v___x_3485_);
                if v_isShared_3533_ == 0 {
                    leanh::lean_ctor_set(v___x_3532_, 0, v___x_3534_);
                    v___x_3536_ = v___x_3532_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 1, v_traceMsgs_3529_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3718_,
                        2,
                        v_expandedMacroDecls_3530_,
                    );
                    v___x_3536_ = v_reuseFailAlloc_3718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v___f_3491_);
                leanh::lean_inc_ref(v___y_3497_);
                leanh::lean_inc(v_ref_3505_);
                v___x_3537_ =
                    leanh::lean_apply_3(v___f_3491_, v_ref_3505_, v___y_3497_, v___x_3536_);
                if leanh::lean_obj_tag(v___x_3537_) == 0 {
                    v_a_3538_ = leanh::lean_ctor_get(v___x_3537_, 0);
                    leanh::lean_inc_n(v_a_3538_, 9);
                    v_a_3539_ = leanh::lean_ctor_get(v___x_3537_, 1);
                    leanh::lean_inc(v_a_3539_);
                    leanh::lean_dec_ref_known(v___x_3537_, 2);
                    leanh::lean_inc(v___x_3509_);
                    v___x_3540_ =
                        l_Lean_Syntax_node2(v___x_3507_, v___x_3509_, v___x_3520_, v___x_3527_);
                    v___x_3541_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                    leanh::lean_inc(v_quotContext_3503_);
                    v___x_3542_ =
                        l_Lean_addMacroScope(v_quotContext_3503_, v___x_3541_, v_macroScope_3528_);
                    v___x_3543_ = l_Lean_mkIdentFrom(v___x_3500_, v___x_3542_, v___x_3487_);
                    leanh::lean_dec(v___x_3500_);
                    v___x_3544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__18;
                    leanh::lean_inc_ref_n(v___x_3490_, 6);
                    leanh::lean_inc_ref_n(v___x_3489_, 6);
                    leanh::lean_inc_ref_n(v___x_3488_, 6);
                    v___x_3545_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3544_);
                    v___x_3546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__19;
                    v___x_3547_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3546_);
                    v___x_3548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__20;
                    v___x_3549_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3549_, 0, v_a_3538_);
                    leanh::lean_ctor_set(v___x_3549_, 1, v___x_3548_);
                    v___x_3550_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__21;
                    v___x_3551_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3551_, 0, v_a_3538_);
                    leanh::lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                    v___x_3552_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3521_, v___x_3551_);
                    v___x_3553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__22;
                    v___x_3554_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3553_);
                    v___x_3555_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                    v___x_3556_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3556_, 0, v_a_3538_);
                    leanh::lean_ctor_set(v___x_3556_, 1, v___x_3521_);
                    leanh::lean_ctor_set(v___x_3556_, 2, v___x_3555_);
                    leanh::lean_inc_ref_n(v___x_3556_, 3);
                    v___x_3557_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3554_, v___x_3556_);
                    v___x_3558_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__24;
                    v___x_3559_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3558_);
                    v___x_3560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__25;
                    v___x_3561_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3560_);
                    v___x_3562_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__26;
                    v___x_3563_ =
                        l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3562_);
                    leanh::lean_inc(v___x_3543_);
                    leanh::lean_inc(v___x_3563_);
                    v___x_3564_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3563_, v___x_3543_);
                    v___x_3565_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__27;
                    v___x_3566_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3566_, 0, v_a_3538_);
                    leanh::lean_ctor_set(v___x_3566_, 1, v___x_3565_);
                    v___x_3567_ = l_Lean_Syntax_node5(
                        v_a_3538_,
                        v___x_3561_,
                        v___x_3564_,
                        v___x_3556_,
                        v___x_3556_,
                        v___x_3566_,
                        v___x_3540_,
                    );
                    leanh::lean_inc_ref(v___y_3497_);
                    leanh::lean_inc(v_ref_3505_);
                    v___x_3568_ = leanh::lean_apply_3(
                        v___f_3491_,
                        v_ref_3505_,
                        v___y_3497_,
                        v_a_3539_,
                    );
                    if leanh::lean_obj_tag(v___x_3568_) == 0 {
                        v_a_3569_ = leanh::lean_ctor_get(v___x_3568_, 0);
                        v_a_3570_ = leanh::lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3699_ =
                            (!leanh::lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v___x_3572_ = v___x_3568_;
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3570_);
                            leanh::lean_inc(v_a_3569_);
                            leanh::lean_dec(v___x_3568_);
                            v___x_3572_ = leanh::lean_box(0);
                            v_isShared_3573_ = v_isSharedCheck_3699_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3567_);
                        leanh::lean_dec(v___x_3563_);
                        leanh::lean_dec(v___x_3559_);
                        leanh::lean_dec(v___x_3557_);
                        leanh::lean_dec_ref_known(v___x_3556_, 3);
                        leanh::lean_dec(v___x_3552_);
                        leanh::lean_dec_ref_known(v___x_3549_, 2);
                        leanh::lean_dec(v___x_3547_);
                        leanh::lean_dec(v___x_3545_);
                        leanh::lean_dec(v___x_3543_);
                        leanh::lean_dec(v_a_3538_);
                        leanh::lean_dec(v___x_3523_);
                        leanh::lean_dec(v___x_3511_);
                        leanh::lean_dec(v___x_3509_);
                        leanh::lean_dec(v___x_3499_);
                        leanh::lean_dec(v_snd_3494_);
                        leanh::lean_dec_ref(v___x_3493_);
                        leanh::lean_dec(v_fst_3492_);
                        leanh::lean_dec_ref(v___x_3490_);
                        leanh::lean_dec_ref(v___x_3489_);
                        leanh::lean_dec_ref(v___x_3488_);
                        v_a_3700_ = leanh::lean_ctor_get(v___x_3568_, 0);
                        v_a_3701_ = leanh::lean_ctor_get(v___x_3568_, 1);
                        v_isSharedCheck_3708_ =
                            (!leanh::lean_is_exclusive(v___x_3568_)) as u8;
                        if v_isSharedCheck_3708_ == 0 {
                            v___x_3703_ = v___x_3568_;
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3701_);
                            leanh::lean_inc(v_a_3700_);
                            leanh::lean_dec(v___x_3568_);
                            v___x_3703_ = leanh::lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3708_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_macroScope_3528_);
                    leanh::lean_dec(v___x_3527_);
                    leanh::lean_dec(v___x_3523_);
                    leanh::lean_dec(v___x_3520_);
                    leanh::lean_dec(v___x_3511_);
                    leanh::lean_dec(v___x_3509_);
                    leanh::lean_dec(v___x_3507_);
                    leanh::lean_dec(v___x_3500_);
                    leanh::lean_dec(v___x_3499_);
                    leanh::lean_dec(v_snd_3494_);
                    leanh::lean_dec_ref(v___x_3493_);
                    leanh::lean_dec(v_fst_3492_);
                    leanh::lean_dec_ref(v___f_3491_);
                    leanh::lean_dec_ref(v___x_3490_);
                    leanh::lean_dec_ref(v___x_3489_);
                    leanh::lean_dec_ref(v___x_3488_);
                    v_a_3709_ = leanh::lean_ctor_get(v___x_3537_, 0);
                    v_a_3710_ = leanh::lean_ctor_get(v___x_3537_, 1);
                    v_isSharedCheck_3717_ = (!leanh::lean_is_exclusive(v___x_3537_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3537_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3710_);
                        leanh::lean_inc(v_a_3709_);
                        leanh::lean_dec(v___x_3537_);
                        v___x_3712_ = leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                leanh::lean_inc_n(v_a_3538_, 2);
                v___x_3574_ = l_Lean_Syntax_node1(v_a_3538_, v___x_3559_, v___x_3567_);
                v___x_3575_ = l_Lean_Syntax_node4(
                    v_a_3538_,
                    v___x_3547_,
                    v___x_3549_,
                    v___x_3552_,
                    v___x_3557_,
                    v___x_3574_,
                );
                leanh::lean_inc_n(v___x_3545_, 4);
                v___x_3576_ = l_Lean_Syntax_node2(v_a_3538_, v___x_3545_, v___x_3575_, v___x_3556_);
                v___x_3577_ = lean_array_push(v_fst_3492_, v___x_3576_);
                v___x_3578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__28;
                leanh::lean_inc_ref_n(v___x_3490_, 11);
                leanh::lean_inc_ref_n(v___x_3489_, 11);
                leanh::lean_inc_ref_n(v___x_3488_, 13);
                v___x_3579_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3578_);
                v___x_3580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__29;
                v___x_3581_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3580_);
                v___x_3582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                leanh::lean_inc_n(v_a_3569_, 54);
                v___x_3583_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3583_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3583_, 1, v___x_3582_);
                v___x_3584_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3584_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3584_, 1, v___x_3521_);
                leanh::lean_ctor_set(v___x_3584_, 2, v___x_3555_);
                v___x_3585_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__31;
                v___x_3586_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3585_);
                v___x_3587_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3587_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3587_, 1, v___x_3512_);
                v___x_3588_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__33);
                v___x_3589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__36;
                leanh::lean_inc_n(v_currMacroScope_3504_, 5);
                leanh::lean_inc_n(v_quotContext_3503_, 5);
                v___x_3590_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3589_, v_currMacroScope_3504_);
                v___x_3591_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__38;
                v___x_3592_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3592_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3592_, 1, v___x_3588_);
                leanh::lean_ctor_set(v___x_3592_, 2, v___x_3590_);
                leanh::lean_ctor_set(v___x_3592_, 3, v___x_3591_);
                v___x_3593_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3511_, v___x_3587_, v___x_3592_);
                v___x_3594_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3594_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3594_, 1, v___x_3524_);
                v___x_3595_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3523_, v___x_3594_);
                leanh::lean_inc(v___x_3543_);
                leanh::lean_inc_n(v___x_3595_, 2);
                v___x_3596_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3595_,
                    v___x_3543_,
                );
                leanh::lean_inc(v___x_3509_);
                v___x_3597_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3509_, v___x_3593_, v___x_3596_);
                leanh::lean_inc_ref_n(v___x_3584_, 9);
                v___x_3598_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3586_, v___x_3584_, v___x_3597_);
                v___x_3599_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3598_);
                v___x_3600_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                v___x_3601_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3601_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3601_, 1, v___x_3600_);
                v___x_3602_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__40;
                v___x_3603_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3602_);
                v___x_3604_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__41;
                v___x_3605_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3604_);
                v___x_3606_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                v___x_3607_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3607_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3607_, 1, v___x_3606_);
                v___x_3608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__44);
                v___x_3609_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__45;
                v___x_3610_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3609_, v_currMacroScope_3504_);
                v___x_3611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__49;
                v___x_3612_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3612_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3612_, 1, v___x_3608_);
                leanh::lean_ctor_set(v___x_3612_, 2, v___x_3610_);
                leanh::lean_ctor_set(v___x_3612_, 3, v___x_3611_);
                v___x_3613_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3612_);
                v___x_3614_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3613_);
                v___x_3615_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                v___x_3616_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3616_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__51;
                v___x_3618_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3617_);
                v___x_3619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__52;
                v___x_3620_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3620_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3620_, 1, v___x_3619_);
                v___x_3621_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3618_, v___x_3620_);
                v___x_3622_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3621_, v___x_3584_);
                v___x_3623_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3622_);
                leanh::lean_inc_n(v___x_3579_, 2);
                v___x_3624_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3579_, v___x_3623_);
                leanh::lean_inc_ref(v___x_3616_);
                leanh::lean_inc_ref(v___x_3607_);
                leanh::lean_inc(v___x_3605_);
                v___x_3625_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3605_,
                    v___x_3607_,
                    v___x_3614_,
                    v___x_3616_,
                    v___x_3624_,
                );
                v___x_3626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__54);
                v___x_3627_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__55;
                v___x_3628_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3627_, v_currMacroScope_3504_);
                v___x_3629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__58;
                v___x_3630_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3630_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3630_, 1, v___x_3626_);
                leanh::lean_ctor_set(v___x_3630_, 2, v___x_3628_);
                leanh::lean_ctor_set(v___x_3630_, 3, v___x_3629_);
                v___x_3631_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__59;
                v___x_3632_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3631_);
                v___x_3633_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__60;
                v___x_3634_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3633_);
                v___x_3635_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__61;
                v___x_3636_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3636_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3636_, 1, v___x_3635_);
                v___x_3637_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__63;
                v___x_3638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__65);
                v___x_3639_ = leanh::lean_box(0);
                v___x_3640_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3639_, v_currMacroScope_3504_);
                v___x_3641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__66;
                v___x_3642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__67;
                v___x_3643_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3641_, v___x_3642_);
                v___x_3644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                v___x_3645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__68;
                v___x_3646_ = l_Lean_Name_mkStr2(v___x_3488_, v___x_3645_);
                v___x_3647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3647_, 0, v___x_3646_);
                v___x_3648_ = l_Lean_Name_mkStr3(v___x_3488_, v___x_3489_, v___x_3490_);
                v___x_3649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                v___x_3650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3650_, 0, v___x_3649_);
                leanh::lean_ctor_set(v___x_3650_, 1, v___x_3517_);
                v___x_3651_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3651_, 0, v___x_3647_);
                leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                v___x_3652_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3652_, 0, v___x_3644_);
                leanh::lean_ctor_set(v___x_3652_, 1, v___x_3651_);
                v___x_3653_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3653_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3653_, 1, v___x_3638_);
                leanh::lean_ctor_set(v___x_3653_, 2, v___x_3640_);
                leanh::lean_ctor_set(v___x_3653_, 3, v___x_3652_);
                v___x_3654_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3637_, v___x_3653_);
                v___x_3655_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3634_, v___x_3636_, v___x_3654_);
                v___x_3656_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3656_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3656_, 1, v___x_3493_);
                v___x_3657_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__70);
                v___x_3658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__71;
                v___x_3659_ =
                    l_Lean_addMacroScope(v_quotContext_3503_, v___x_3658_, v_currMacroScope_3504_);
                v___x_3660_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3660_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3660_, 1, v___x_3657_);
                leanh::lean_ctor_set(v___x_3660_, 2, v___x_3659_);
                leanh::lean_ctor_set(v___x_3660_, 3, v___x_3517_);
                leanh::lean_inc_ref(v___x_3660_);
                v___x_3661_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3660_);
                v___x_3662_ = l_Lean_Syntax_node3(
                    v_a_3569_,
                    v___x_3521_,
                    v___x_3499_,
                    v___x_3656_,
                    v___x_3661_,
                );
                v___x_3663_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__72;
                v___x_3664_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3664_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3664_, 1, v___x_3663_);
                v___x_3665_ = l_Lean_Syntax_node3(
                    v_a_3569_,
                    v___x_3632_,
                    v___x_3655_,
                    v___x_3662_,
                    v___x_3664_,
                );
                v___x_3666_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3665_);
                v___x_3667_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3509_, v___x_3630_, v___x_3666_);
                v___x_3668_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3667_);
                v___x_3669_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3668_);
                v___x_3670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__73;
                v___x_3671_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3670_);
                v___x_3672_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__74;
                v___x_3673_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3672_);
                v___x_3674_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3563_, v___x_3543_);
                v___x_3675_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3675_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3675_, 1, v___x_3565_);
                v___x_3676_ = l_Lean_Syntax_node5(
                    v_a_3569_,
                    v___x_3673_,
                    v___x_3674_,
                    v___x_3584_,
                    v___x_3584_,
                    v___x_3675_,
                    v___x_3660_,
                );
                v___x_3677_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3671_, v___x_3676_);
                v___x_3678_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3677_, v___x_3584_);
                v___x_3679_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__75;
                v___x_3680_ =
                    l_Lean_Name_mkStr4(v___x_3488_, v___x_3489_, v___x_3490_, v___x_3679_);
                v___x_3681_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76;
                v___x_3682_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3682_, 0, v_a_3569_);
                leanh::lean_ctor_set(v___x_3682_, 1, v___x_3681_);
                v___x_3683_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3680_, v___x_3682_, v_snd_3494_);
                v___x_3684_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3683_, v___x_3584_);
                v___x_3685_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3521_, v___x_3678_, v___x_3684_);
                v___x_3686_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3579_, v___x_3685_);
                v___x_3687_ = l_Lean_Syntax_node4(
                    v_a_3569_,
                    v___x_3605_,
                    v___x_3607_,
                    v___x_3669_,
                    v___x_3616_,
                    v___x_3686_,
                );
                v___x_3688_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3521_, v___x_3625_, v___x_3687_);
                v___x_3689_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3603_, v___x_3688_);
                v___x_3690_ = l_Lean_Syntax_node7(
                    v_a_3569_,
                    v___x_3581_,
                    v___x_3583_,
                    v___x_3584_,
                    v___x_3584_,
                    v___x_3584_,
                    v___x_3599_,
                    v___x_3601_,
                    v___x_3689_,
                );
                v___x_3691_ = l_Lean_Syntax_node2(v_a_3569_, v___x_3545_, v___x_3690_, v___x_3584_);
                v___x_3692_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3521_, v___x_3691_);
                v___x_3693_ = l_Lean_Syntax_node1(v_a_3569_, v___x_3579_, v___x_3692_);
                v___x_3694_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3694_, 0, v___x_3577_);
                leanh::lean_ctor_set(v___x_3694_, 1, v___x_3693_);
                v___x_3695_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3695_, 0, v___x_3694_);
                if v_isShared_3573_ == 0 {
                    leanh::lean_ctor_set(v___x_3572_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3572_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_a_3570_);
                    v___x_3697_ = v_reuseFailAlloc_3698_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3697_;
            }
            6 => {
                if v_isShared_3704_ == 0 {
                    v___x_3706_ = v___x_3703_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 1, v_a_3701_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3706_;
            }
            8 => {
                if v_isShared_3713_ == 0 {
                    v___x_3715_ = v___x_3712_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3716_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 1, v_a_3710_);
                    v___x_3715_ = v_reuseFailAlloc_3716_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3715_;
            }
            10 => {
                if v_isShared_3728_ == 0 {
                    v___x_3730_ = v___x_3727_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3731_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3731_, 1, v_a_3725_);
                    v___x_3730_ = v_reuseFailAlloc_3731_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3730_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___boxed(
    mut v___x_3733_: *mut leanh::LeanObject,
    mut v___x_3734_: *mut leanh::LeanObject,
    mut v___x_3735_: *mut leanh::LeanObject,
    mut v___x_3736_: *mut leanh::LeanObject,
    mut v___x_3737_: *mut leanh::LeanObject,
    mut v___x_3738_: *mut leanh::LeanObject,
    mut v___x_3739_: *mut leanh::LeanObject,
    mut v___f_3740_: *mut leanh::LeanObject,
    mut v_fst_3741_: *mut leanh::LeanObject,
    mut v___x_3742_: *mut leanh::LeanObject,
    mut v_snd_3743_: *mut leanh::LeanObject,
    mut v_x_3744_: *mut leanh::LeanObject,
    mut v_h_x3f_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146124__boxed_3748_: u8 = 0;
    let mut v_res_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146124__boxed_3748_ = (leanh::lean_unbox(v___x_3736_) as u8);
    v_res_3749_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(
            v___x_3733_,
            v___x_3734_,
            v___x_3735_,
            v___x_146124__boxed_3748_,
            v___x_3737_,
            v___x_3738_,
            v___x_3739_,
            v___f_3740_,
            v_fst_3741_,
            v___x_3742_,
            v_snd_3743_,
            v_x_3744_,
            v_h_x3f_3745_,
            v___y_3746_,
            v___y_3747_,
        );
    leanh::lean_dec_ref(v___y_3746_);
    leanh::lean_dec(v_h_x3f_3745_);
    leanh::lean_dec(v___x_3735_);
    leanh::lean_dec(v___x_3734_);
    leanh::lean_dec(v___x_3733_);
    return v_res_3749_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
    mut v___x_3750_: u8,
    mut v_____do__lift_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_SourceInfo_fromRef(v_____do__lift_3751_, v___x_3750_);
    v___x_3755_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3755_, 0, v___x_3754_);
    leanh::lean_ctor_set(v___x_3755_, 1, v___y_3753_);
    return v___x_3755_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed(
    mut v___x_3756_: *mut leanh::LeanObject,
    mut v_____do__lift_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146730__boxed_3760_: u8 = 0;
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146730__boxed_3760_ = (leanh::lean_unbox(v___x_3756_) as u8);
    v_res_3761_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0(
            v___x_146730__boxed_3760_,
            v_____do__lift_3757_,
            v___y_3758_,
            v___y_3759_,
        );
    leanh::lean_dec_ref(v___y_3758_);
    leanh::lean_dec(v_____do__lift_3757_);
    return v_res_3761_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
    mut v___x_3772_: u8,
    mut v_a_3773_: *mut leanh::LeanObject,
    mut v_b_3774_: *mut leanh::LeanObject,
    mut v___y_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: u8 = 0;
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v_a_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_unused_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3859_: u8 = 0;
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3863_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v_isSharedCheck_3873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3777_ = leanh::lean_ctor_get(v_a_3773_, 0);
                v_start_3778_ = leanh::lean_ctor_get(v_a_3773_, 1);
                v_stop_3779_ = leanh::lean_ctor_get(v_a_3773_, 2);
                v_isSharedCheck_3873_ = (!leanh::lean_is_exclusive(v_a_3773_)) as u8;
                if v_isSharedCheck_3873_ == 0 {
                    v___x_3781_ = v_a_3773_;
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3779_);
                    leanh::lean_inc(v_start_3778_);
                    leanh::lean_inc(v_array_3777_);
                    leanh::lean_dec(v_a_3773_);
                    v___x_3781_ = leanh::lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3783_ = lean_nat_dec_lt(v_start_3778_, v_stop_3779_);
                if v___x_3783_ == 0 {
                    leanh::lean_del_object(v___x_3781_);
                    leanh::lean_dec(v_stop_3779_);
                    leanh::lean_dec(v_start_3778_);
                    leanh::lean_dec_ref(v_array_3777_);
                    v___x_3784_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3784_, 0, v_b_3774_);
                    leanh::lean_ctor_set(v___x_3784_, 1, v___y_3776_);
                    return v___x_3784_;
                } else {
                    v_fst_3785_ = leanh::lean_ctor_get(v_b_3774_, 0);
                    v_snd_3786_ = leanh::lean_ctor_get(v_b_3774_, 1);
                    v_isSharedCheck_3872_ = (!leanh::lean_is_exclusive(v_b_3774_)) as u8;
                    if v_isSharedCheck_3872_ == 0 {
                        v___x_3788_ = v_b_3774_;
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3786_);
                        leanh::lean_inc(v_fst_3785_);
                        leanh::lean_dec(v_b_3774_);
                        v___x_3788_ = leanh::lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3872_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3790_ = leanh::lean_unsigned_to_nat(1);
                v___x_3791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__0;
                v___x_3792_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__1;
                v___x_3793_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__2;
                v___x_3794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                v___x_3795_ = lean_nat_add(v_start_3778_, v___x_3790_);
                leanh::lean_inc_ref(v_array_3777_);
                if v_isShared_3782_ == 0 {
                    leanh::lean_ctor_set(v___x_3781_, 1, v___x_3795_);
                    v___x_3797_ = v___x_3781_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_array_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___x_3795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3871_, 2, v_stop_3779_);
                    v___x_3797_ = v_reuseFailAlloc_3871_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3823_ = lean_array_fget(v_array_3777_, v_start_3778_);
                leanh::lean_dec(v_start_3778_);
                leanh::lean_dec_ref(v_array_3777_);
                leanh::lean_inc(v___x_3823_);
                v___x_3824_ = l_Lean_Syntax_isOfKind(v___x_3823_, v___x_3794_);
                if v___x_3824_ == 0 {
                    leanh::lean_dec(v___x_3823_);
                    v___x_3825_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                    if leanh::lean_obj_tag(v___x_3825_) == 0 {
                        v_a_3826_ = leanh::lean_ctor_get(v___x_3825_, 1);
                        leanh::lean_inc(v_a_3826_);
                        leanh::lean_dec_ref_known(v___x_3825_, 2);
                        if v_isShared_3789_ == 0 {
                            v___x_3828_ = v___x_3788_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_3830_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_fst_3785_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_snd_3786_);
                            v___x_3828_ = v_reuseFailAlloc_3830_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3797_);
                        leanh::lean_del_object(v___x_3788_);
                        leanh::lean_dec(v_snd_3786_);
                        leanh::lean_dec(v_fst_3785_);
                        v_a_3831_ = leanh::lean_ctor_get(v___x_3825_, 0);
                        v_a_3832_ = leanh::lean_ctor_get(v___x_3825_, 1);
                        v_isSharedCheck_3839_ =
                            (!leanh::lean_is_exclusive(v___x_3825_)) as u8;
                        if v_isSharedCheck_3839_ == 0 {
                            v___x_3834_ = v___x_3825_;
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3832_);
                            leanh::lean_inc(v_a_3831_);
                            leanh::lean_dec(v___x_3825_);
                            v___x_3834_ = leanh::lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    v___x_3840_ = leanh::lean_box((v___x_3772_) as usize);
                    v___f_3841_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                    leanh::lean_closure_set(v___f_3841_, 0, v___x_3840_);
                    v___x_3842_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__5;
                    v___x_3844_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3845_ = l_Lean_Syntax_getArg(v___x_3823_, v___x_3844_);
                    v___x_3846_ = l_Lean_Syntax_isNone(v___x_3845_);
                    if v___x_3846_ == 0 {
                        v___x_3847_ = leanh::lean_unsigned_to_nat(2);
                        leanh::lean_inc(v___x_3845_);
                        v___x_3848_ = l_Lean_Syntax_matchesNull(v___x_3845_, v___x_3847_);
                        if v___x_3848_ == 0 {
                            leanh::lean_dec(v___x_3845_);
                            leanh::lean_dec_ref(v___f_3841_);
                            leanh::lean_dec(v___x_3823_);
                            v___x_3849_ = l_Lean_Macro_throwUnsupported___redArg(v___y_3776_);
                            if leanh::lean_obj_tag(v___x_3849_) == 0 {
                                v_a_3850_ = leanh::lean_ctor_get(v___x_3849_, 1);
                                leanh::lean_inc(v_a_3850_);
                                leanh::lean_dec_ref_known(v___x_3849_, 2);
                                if v_isShared_3789_ == 0 {
                                    v___x_3852_ = v___x_3788_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3854_ =
                                        leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3854_,
                                        0,
                                        v_fst_3785_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3854_,
                                        1,
                                        v_snd_3786_,
                                    );
                                    v___x_3852_ = v_reuseFailAlloc_3854_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3797_);
                                leanh::lean_del_object(v___x_3788_);
                                leanh::lean_dec(v_snd_3786_);
                                leanh::lean_dec(v_fst_3785_);
                                v_a_3855_ = leanh::lean_ctor_get(v___x_3849_, 0);
                                v_a_3856_ = leanh::lean_ctor_get(v___x_3849_, 1);
                                v_isSharedCheck_3863_ =
                                    (!leanh::lean_is_exclusive(v___x_3849_)) as u8;
                                if v_isSharedCheck_3863_ == 0 {
                                    v___x_3858_ = v___x_3849_;
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3856_);
                                    leanh::lean_inc(v_a_3855_);
                                    leanh::lean_dec(v___x_3849_);
                                    v___x_3858_ = leanh::lean_box(0);
                                    v_isShared_3859_ = v_isSharedCheck_3863_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3788_);
                            v___x_3864_ = l_Lean_Syntax_getArg(v___x_3845_, v___x_3844_);
                            leanh::lean_dec(v___x_3845_);
                            v___x_3865_ = leanh::lean_box(0);
                            v___x_3866_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                            v___x_3867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3865_, v___x_3866_, v___y_3775_, v___y_3776_);
                            leanh::lean_dec_ref_known(v___x_3866_, 1);
                            leanh::lean_dec(v___x_3823_);
                            v___y_3799_ = v___x_3867_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3845_);
                        leanh::lean_del_object(v___x_3788_);
                        v___x_3868_ = leanh::lean_box(0);
                        v___x_3869_ = leanh::lean_box(0);
                        v___x_3870_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1(v___x_3823_, v___x_3790_, v___x_3842_, v___x_3772_, v___x_3791_, v___x_3792_, v___x_3793_, v___f_3841_, v_fst_3785_, v___x_3843_, v_snd_3786_, v___x_3868_, v___x_3869_, v___y_3775_, v___y_3776_);
                        leanh::lean_dec(v___x_3823_);
                        v___y_3799_ = v___x_3870_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v___y_3799_) == 0 {
                    v_a_3800_ = leanh::lean_ctor_get(v___y_3799_, 0);
                    leanh::lean_inc(v_a_3800_);
                    if leanh::lean_obj_tag(v_a_3800_) == 0 {
                        leanh::lean_dec_ref(v___x_3797_);
                        v_a_3801_ = leanh::lean_ctor_get(v___y_3799_, 1);
                        v_isSharedCheck_3809_ =
                            (!leanh::lean_is_exclusive(v___y_3799_)) as u8;
                        if v_isSharedCheck_3809_ == 0 {
                            v_unused_3810_ = leanh::lean_ctor_get(v___y_3799_, 0);
                            leanh::lean_dec(v_unused_3810_);
                            v___x_3803_ = v___y_3799_;
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3801_);
                            leanh::lean_dec(v___y_3799_);
                            v___x_3803_ = leanh::lean_box(0);
                            v_isShared_3804_ = v_isSharedCheck_3809_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_3811_ = leanh::lean_ctor_get(v___y_3799_, 1);
                        leanh::lean_inc(v_a_3811_);
                        leanh::lean_dec_ref_known(v___y_3799_, 2);
                        v_a_3812_ = leanh::lean_ctor_get(v_a_3800_, 0);
                        leanh::lean_inc(v_a_3812_);
                        leanh::lean_dec_ref_known(v_a_3800_, 1);
                        v_a_3773_ = v___x_3797_;
                        v_b_3774_ = v_a_3812_;
                        v___y_3776_ = v_a_3811_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3797_);
                    v_a_3814_ = leanh::lean_ctor_get(v___y_3799_, 0);
                    v_a_3815_ = leanh::lean_ctor_get(v___y_3799_, 1);
                    v_isSharedCheck_3822_ = (!leanh::lean_is_exclusive(v___y_3799_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v___x_3817_ = v___y_3799_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3815_);
                        leanh::lean_inc(v_a_3814_);
                        leanh::lean_dec(v___y_3799_);
                        v___x_3817_ = leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v_a_3805_ = leanh::lean_ctor_get(v_a_3800_, 0);
                leanh::lean_inc(v_a_3805_);
                leanh::lean_dec_ref_known(v_a_3800_, 1);
                if v_isShared_3804_ == 0 {
                    leanh::lean_ctor_set(v___x_3803_, 0, v_a_3805_);
                    v___x_3807_ = v___x_3803_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_a_3801_);
                    v___x_3807_ = v_reuseFailAlloc_3808_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3807_;
            }
            7 => {
                if v_isShared_3818_ == 0 {
                    v___x_3820_ = v___x_3817_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_a_3815_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3820_;
            }
            9 => {
                v_a_3773_ = v___x_3797_;
                v_b_3774_ = v___x_3828_;
                v___y_3776_ = v_a_3826_;
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3837_;
            }
            12 => {
                v_a_3773_ = v___x_3797_;
                v_b_3774_ = v___x_3852_;
                v___y_3776_ = v_a_3850_;
                state = 0;
                continue;
            }
            13 => {
                if v_isShared_3859_ == 0 {
                    v___x_3861_ = v___x_3858_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3862_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3856_);
                    v___x_3861_ = v_reuseFailAlloc_3862_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___boxed(
    mut v___x_3874_: *mut leanh::LeanObject,
    mut v_a_3875_: *mut leanh::LeanObject,
    mut v_b_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_146766__boxed_3879_: u8 = 0;
    let mut v_res_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_146766__boxed_3879_ = (leanh::lean_unbox(v___x_3874_) as u8);
    v_res_3880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
        v___x_146766__boxed_3879_,
        v_a_3875_,
        v_b_3876_,
        v___y_3877_,
        v___y_3878_,
    );
    leanh::lean_dec_ref(v___y_3877_);
    return v_res_3880_;
}
pub unsafe fn l_Lean_Elab_Do_expandDoFor(
    mut v_stx_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v_ref_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4016_: u8 = 0;
    let mut v_a_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4021_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4025_: u8 = 0;
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4095_: u8 = 0;
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4173_: u8 = 0;
    let mut v_x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v_ref_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4209_: u8 = 0;
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v___y_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: u8 = 0;
    let mut v___y_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: u8 = 0;
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4266_: u8 = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v___y_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u8 = 0;
    let mut v_decls_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: u8 = 0;
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: u8 = 0;
    let mut v_decls_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_ref_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4374_: u8 = 0;
    let mut v_a_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4379_: u8 = 0;
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4437_: u8 = 0;
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4441_: u8 = 0;
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4449_: u8 = 0;
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4453_: u8 = 0;
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: u8 = 0;
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: u8 = 0;
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v_decls_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4486_: u8 = 0;
    let mut v_ref_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4507_: u8 = 0;
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4511_: u8 = 0;
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doElems_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4565_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: u8 = 0;
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3940_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                leanh::lean_inc(v_stx_3937_);
                v___x_3941_ = l_Lean_Syntax_isOfKind(v_stx_3937_, v___x_3940_);
                if v___x_3941_ == 0 {
                    leanh::lean_dec(v_stx_3937_);
                    v___x_3942_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                    return v___x_3942_;
                } else {
                    v___x_3943_ = leanh::lean_unsigned_to_nat(0);
                    v_tk_3944_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3943_);
                    v___x_3945_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3946_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_3945_);
                    leanh::lean_inc(v___x_3946_);
                    v___x_3947_ = l_Lean_Syntax_matchesNull(v___x_3946_, v___x_3945_);
                    if v___x_3947_ == 0 {
                        v___x_3948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        v_decls_3980_ = l_Lean_Syntax_getArgs(v___x_3946_);
                        leanh::lean_dec(v___x_3946_);
                        v_decls_3981_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_3980_);
                        leanh::lean_dec_ref(v_decls_3980_);
                        v___x_4026_ = leanh::lean_box(0);
                        v___x_4027_ = lean_array_get(v___x_4026_, v_decls_3981_, v___x_3943_);
                        leanh::lean_inc(v___x_4027_);
                        v___x_4028_ = l_Lean_Syntax_isOfKind(v___x_4027_, v___x_3948_);
                        if v___x_4028_ == 0 {
                            leanh::lean_dec(v___x_4027_);
                            leanh::lean_dec_ref(v_decls_3981_);
                            leanh::lean_dec(v_tk_3944_);
                            leanh::lean_dec(v_stx_3937_);
                            v___x_4029_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                            return v___x_4029_;
                        } else {
                            v___x_4030_ = leanh::lean_unsigned_to_nat(3);
                            v_body_4031_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4030_);
                            leanh::lean_dec(v_stx_3937_);
                            v___x_4096_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3943_);
                            v___x_4097_ = l_Lean_Syntax_isNone(v___x_4096_);
                            if v___x_4097_ == 0 {
                                v___x_4098_ = leanh::lean_unsigned_to_nat(2);
                                leanh::lean_inc(v___x_4096_);
                                v___x_4099_ = l_Lean_Syntax_matchesNull(v___x_4096_, v___x_4098_);
                                if v___x_4099_ == 0 {
                                    leanh::lean_dec(v___x_4096_);
                                    leanh::lean_dec(v_body_4031_);
                                    leanh::lean_dec(v___x_4027_);
                                    leanh::lean_dec_ref(v_decls_3981_);
                                    leanh::lean_dec(v_tk_3944_);
                                    v___x_4100_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                    return v___x_4100_;
                                } else {
                                    v_h_x3f_4101_ = l_Lean_Syntax_getArg(v___x_4096_, v___x_3943_);
                                    leanh::lean_dec(v___x_4096_);
                                    v___x_4102_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4102_, 0, v_h_x3f_4101_);
                                    v_h_x3f_4033_ = v___x_4102_;
                                    v___y_4034_ = v_a_3938_;
                                    v___y_4035_ = v_a_3939_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_4096_);
                                v___x_4103_ = leanh::lean_box(0);
                                v_h_x3f_4033_ = v___x_4103_;
                                v___y_4034_ = v_a_3938_;
                                v___y_4035_ = v_a_3939_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        v___x_4104_ = l_Lean_Syntax_getArg(v___x_3946_, v___x_3943_);
                        v___x_4105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        leanh::lean_inc(v___x_4104_);
                        v___x_4337_ = l_Lean_Syntax_isOfKind(v___x_4104_, v___x_4105_);
                        if v___x_4337_ == 0 {
                            leanh::lean_dec(v___x_4104_);
                            v_decls_4338_ = l_Lean_Syntax_getArgs(v___x_3946_);
                            leanh::lean_dec(v___x_3946_);
                            v_decls_4339_ =
                                l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4338_);
                            leanh::lean_dec_ref(v_decls_4338_);
                            v___x_4384_ = leanh::lean_box(0);
                            v___x_4385_ = lean_array_get(v___x_4384_, v_decls_4339_, v___x_3943_);
                            leanh::lean_inc(v___x_4385_);
                            v___x_4386_ = l_Lean_Syntax_isOfKind(v___x_4385_, v___x_4105_);
                            if v___x_4386_ == 0 {
                                leanh::lean_dec(v___x_4385_);
                                leanh::lean_dec_ref(v_decls_4339_);
                                leanh::lean_dec(v_tk_3944_);
                                leanh::lean_dec(v_stx_3937_);
                                v___x_4387_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                return v___x_4387_;
                            } else {
                                v___x_4388_ = leanh::lean_unsigned_to_nat(3);
                                v_body_4389_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4388_);
                                leanh::lean_dec(v_stx_3937_);
                                v___x_4454_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_3943_);
                                v___x_4455_ = l_Lean_Syntax_isNone(v___x_4454_);
                                if v___x_4455_ == 0 {
                                    v___x_4456_ = leanh::lean_unsigned_to_nat(2);
                                    leanh::lean_inc(v___x_4454_);
                                    v___x_4457_ =
                                        l_Lean_Syntax_matchesNull(v___x_4454_, v___x_4456_);
                                    if v___x_4457_ == 0 {
                                        leanh::lean_dec(v___x_4454_);
                                        leanh::lean_dec(v_body_4389_);
                                        leanh::lean_dec(v___x_4385_);
                                        leanh::lean_dec_ref(v_decls_4339_);
                                        leanh::lean_dec(v_tk_3944_);
                                        v___x_4458_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4458_;
                                    } else {
                                        v_h_x3f_4459_ =
                                            l_Lean_Syntax_getArg(v___x_4454_, v___x_3943_);
                                        leanh::lean_dec(v___x_4454_);
                                        v___x_4460_ =
                                            leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_4460_, 0, v_h_x3f_4459_);
                                        v_h_x3f_4391_ = v___x_4460_;
                                        v___y_4392_ = v_a_3938_;
                                        v___y_4393_ = v_a_3939_;
                                        state = 31;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v___x_4454_);
                                    v___x_4461_ = leanh::lean_box(0);
                                    v_h_x3f_4391_ = v___x_4461_;
                                    v___y_4392_ = v_a_3938_;
                                    v___y_4393_ = v_a_3939_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            v___x_4462_ = l_Lean_Syntax_getArg(v___x_4104_, v___x_3943_);
                            v___x_4463_ = l_Lean_Syntax_isNone(v___x_4462_);
                            if v___x_4463_ == 0 {
                                v___x_4464_ = leanh::lean_unsigned_to_nat(2);
                                v___x_4465_ = l_Lean_Syntax_matchesNull(v___x_4462_, v___x_4464_);
                                if v___x_4465_ == 0 {
                                    leanh::lean_dec(v___x_4104_);
                                    v_decls_4466_ = l_Lean_Syntax_getArgs(v___x_3946_);
                                    leanh::lean_dec(v___x_3946_);
                                    v_decls_4467_ =
                                        l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4466_);
                                    leanh::lean_dec_ref(v_decls_4466_);
                                    v___x_4512_ = leanh::lean_box(0);
                                    v___x_4513_ =
                                        lean_array_get(v___x_4512_, v_decls_4467_, v___x_3943_);
                                    leanh::lean_inc(v___x_4513_);
                                    v___x_4514_ = l_Lean_Syntax_isOfKind(v___x_4513_, v___x_4105_);
                                    if v___x_4514_ == 0 {
                                        leanh::lean_dec(v___x_4513_);
                                        leanh::lean_dec_ref(v_decls_4467_);
                                        leanh::lean_dec(v_tk_3944_);
                                        leanh::lean_dec(v_stx_3937_);
                                        v___x_4515_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3939_);
                                        return v___x_4515_;
                                    } else {
                                        v___x_4516_ = leanh::lean_unsigned_to_nat(3);
                                        v_body_4517_ =
                                            l_Lean_Syntax_getArg(v_stx_3937_, v___x_4516_);
                                        leanh::lean_dec(v_stx_3937_);
                                        v___x_4582_ =
                                            l_Lean_Syntax_getArg(v___x_4513_, v___x_3943_);
                                        v___x_4583_ = l_Lean_Syntax_isNone(v___x_4582_);
                                        if v___x_4583_ == 0 {
                                            leanh::lean_inc(v___x_4582_);
                                            v___x_4584_ =
                                                l_Lean_Syntax_matchesNull(v___x_4582_, v___x_4464_);
                                            if v___x_4584_ == 0 {
                                                leanh::lean_dec(v___x_4582_);
                                                leanh::lean_dec(v_body_4517_);
                                                leanh::lean_dec(v___x_4513_);
                                                leanh::lean_dec_ref(v_decls_4467_);
                                                leanh::lean_dec(v_tk_3944_);
                                                v___x_4585_ =
                                                    l_Lean_Macro_throwUnsupported___redArg(
                                                        v_a_3939_,
                                                    );
                                                return v___x_4585_;
                                            } else {
                                                v_h_x3f_4586_ =
                                                    l_Lean_Syntax_getArg(v___x_4582_, v___x_3943_);
                                                leanh::lean_dec(v___x_4582_);
                                                v___x_4587_ =
                                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_4587_,
                                                    0,
                                                    v_h_x3f_4586_,
                                                );
                                                v_h_x3f_4519_ = v___x_4587_;
                                                v___y_4520_ = v_a_3938_;
                                                v___y_4521_ = v_a_3939_;
                                                state = 41;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v___x_4582_);
                                            v___x_4588_ = leanh::lean_box(0);
                                            v_h_x3f_4519_ = v___x_4588_;
                                            v___y_4520_ = v_a_3938_;
                                            v___y_4521_ = v_a_3939_;
                                            state = 41;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___y_4284_ = v_a_3938_;
                                    v___y_4285_ = v_a_3939_;
                                    state = 24;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_4462_);
                                v___y_4284_ = v_a_3938_;
                                v___y_4285_ = v_a_3939_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref_n(v___y_3953_, 3);
                v___x_3961_ = l_Array_append___redArg(v___y_3953_, v___y_3960_);
                leanh::lean_dec_ref(v___y_3960_);
                leanh::lean_inc_n(v___y_3959_, 4);
                leanh::lean_inc_n(v___y_3952_, 10);
                v___x_3962_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3962_, 0, v___y_3952_);
                leanh::lean_ctor_set(v___x_3962_, 1, v___y_3959_);
                leanh::lean_ctor_set(v___x_3962_, 2, v___x_3961_);
                v___x_3963_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_3964_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3964_, 0, v___y_3952_);
                leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = l_Lean_Syntax_node4(
                    v___y_3952_,
                    v___x_3948_,
                    v___x_3962_,
                    v___y_3951_,
                    v___x_3964_,
                    v___y_3954_,
                );
                v___x_3966_ = l_Lean_Syntax_node1(v___y_3952_, v___y_3959_, v___x_3965_);
                v___x_3967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76;
                v___x_3968_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3968_, 0, v___y_3952_);
                leanh::lean_ctor_set(v___x_3968_, 1, v___x_3967_);
                leanh::lean_inc_ref(v___x_3968_);
                v___x_3969_ = l_Lean_Syntax_node4(
                    v___y_3952_,
                    v___x_3940_,
                    v___y_3958_,
                    v___x_3966_,
                    v___x_3968_,
                    v___y_3950_,
                );
                v___x_3970_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3970_, 0, v___y_3952_);
                leanh::lean_ctor_set(v___x_3970_, 1, v___y_3959_);
                leanh::lean_ctor_set(v___x_3970_, 2, v___y_3953_);
                leanh::lean_inc(v___y_3957_);
                v___x_3971_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___y_3957_, v___x_3969_, v___x_3970_);
                v___x_3972_ = lean_array_push(v___y_3956_, v___x_3971_);
                v___x_3973_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_3974_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_3975_ = l_Array_append___redArg(v___y_3953_, v___x_3972_);
                leanh::lean_dec_ref(v___x_3972_);
                v___x_3976_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3976_, 0, v___y_3952_);
                leanh::lean_ctor_set(v___x_3976_, 1, v___y_3959_);
                leanh::lean_ctor_set(v___x_3976_, 2, v___x_3975_);
                v___x_3977_ = l_Lean_Syntax_node1(v___y_3952_, v___x_3974_, v___x_3976_);
                v___x_3978_ =
                    l_Lean_Syntax_node2(v___y_3952_, v___x_3973_, v___x_3968_, v___x_3977_);
                v___x_3979_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3979_, 0, v___x_3978_);
                leanh::lean_ctor_set(v___x_3979_, 1, v___y_3955_);
                return v___x_3979_;
            }
            2 => {
                v___x_3990_ = lean_array_get_size(v_decls_3981_);
                v___x_3991_ = l_Array_toSubarray___redArg(v_decls_3981_, v___x_3945_, v___x_3990_);
                leanh::lean_inc_ref(v___y_3983_);
                v___x_3992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3992_, 0, v___y_3983_);
                leanh::lean_ctor_set(v___x_3992_, 1, v_body_3987_);
                v___x_3993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_3947_, v___x_3991_, v___x_3992_, v___y_3988_, v___y_3989_);
                if leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = leanh::lean_ctor_get(v___x_3993_, 0);
                    leanh::lean_inc(v_a_3994_);
                    v_a_3995_ = leanh::lean_ctor_get(v___x_3993_, 1);
                    leanh::lean_inc(v_a_3995_);
                    leanh::lean_dec_ref_known(v___x_3993_, 2);
                    v_fst_3996_ = leanh::lean_ctor_get(v_a_3994_, 0);
                    v_snd_3997_ = leanh::lean_ctor_get(v_a_3994_, 1);
                    v_isSharedCheck_4016_ = (!leanh::lean_is_exclusive(v_a_3994_)) as u8;
                    if v_isSharedCheck_4016_ == 0 {
                        v___x_3999_ = v_a_3994_;
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3997_);
                        leanh::lean_inc(v_fst_3996_);
                        leanh::lean_dec(v_a_3994_);
                        v___x_3999_ = leanh::lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4016_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_3986_);
                    leanh::lean_dec(v___y_3985_);
                    leanh::lean_dec(v___y_3984_);
                    leanh::lean_dec(v_tk_3944_);
                    v_a_4017_ = leanh::lean_ctor_get(v___x_3993_, 0);
                    v_a_4018_ = leanh::lean_ctor_get(v___x_3993_, 1);
                    v_isSharedCheck_4025_ = (!leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4025_ == 0 {
                        v___x_4020_ = v___x_3993_;
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4018_);
                        leanh::lean_inc(v_a_4017_);
                        leanh::lean_dec(v___x_3993_);
                        v___x_4020_ = leanh::lean_box(0);
                        v_isShared_4021_ = v_isSharedCheck_4025_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_ref_4001_ = leanh::lean_ctor_get(v___y_3988_, 5);
                v___x_4002_ = l_Lean_SourceInfo_fromRef(v_ref_4001_, v___x_3947_);
                v___x_4003_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4004_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                leanh::lean_dec(v_tk_3944_);
                v___x_4005_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4000_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3999_, 2);
                    leanh::lean_ctor_set(v___x_3999_, 1, v___x_4005_);
                    leanh::lean_ctor_set(v___x_3999_, 0, v___x_4004_);
                    v___x_4007_ = v___x_3999_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4015_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4015_, 1, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4015_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4009_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if leanh::lean_obj_tag(v___y_3985_) == 1 {
                    v_val_4010_ = leanh::lean_ctor_get(v___y_3985_, 0);
                    leanh::lean_inc(v_val_4010_);
                    leanh::lean_dec_ref_known(v___y_3985_, 1);
                    v___x_4011_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    leanh::lean_inc(v___x_4002_);
                    v___x_4012_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4012_, 0, v___x_4002_);
                    leanh::lean_ctor_set(v___x_4012_, 1, v___x_4011_);
                    v___x_4013_ = l_Array_mkArray2___redArg(v_val_4010_, v___x_4012_);
                    v___y_3950_ = v_snd_3997_;
                    v___y_3951_ = v_x_3986_;
                    v___y_3952_ = v___x_4002_;
                    v___y_3953_ = v___x_4009_;
                    v___y_3954_ = v___y_3984_;
                    v___y_3955_ = v_a_3995_;
                    v___y_3956_ = v_fst_3996_;
                    v___y_3957_ = v___x_4003_;
                    v___y_3958_ = v___x_4007_;
                    v___y_3959_ = v___x_4008_;
                    v___y_3960_ = v___x_4013_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_3985_);
                    v___x_4014_ = l_Lean_Elab_Do_expandDoFor___closed__8;
                    v___y_3950_ = v_snd_3997_;
                    v___y_3951_ = v_x_3986_;
                    v___y_3952_ = v___x_4002_;
                    v___y_3953_ = v___x_4009_;
                    v___y_3954_ = v___y_3984_;
                    v___y_3955_ = v_a_3995_;
                    v___y_3956_ = v_fst_3996_;
                    v___y_3957_ = v___x_4003_;
                    v___y_3958_ = v___x_4007_;
                    v___y_3959_ = v___x_4008_;
                    v___y_3960_ = v___x_4014_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_4021_ == 0 {
                    v___x_4023_ = v___x_4020_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4024_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4024_, 1, v_a_4018_);
                    v___x_4023_ = v_reuseFailAlloc_4024_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4023_;
            }
            7 => {
                v___x_4036_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_3945_);
                v___x_4037_ = l_Lean_Syntax_getArg(v___x_4027_, v___x_4030_);
                leanh::lean_dec(v___x_4027_);
                v_doElems_4038_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4039_ = l_Lean_Syntax_isIdent(v___x_4036_);
                if v___x_4039_ == 0 {
                    v___x_4040_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    leanh::lean_inc(v___x_4036_);
                    v___x_4041_ = l_Lean_Syntax_isOfKind(v___x_4036_, v___x_4040_);
                    if v___x_4041_ == 0 {
                        v___x_4042_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4036_,
                                v___x_4041_,
                                v___y_4034_,
                                v___y_4035_,
                            );
                        if leanh::lean_obj_tag(v___x_4042_) == 0 {
                            v_a_4043_ = leanh::lean_ctor_get(v___x_4042_, 0);
                            leanh::lean_inc_n(v_a_4043_, 2);
                            v_a_4044_ = leanh::lean_ctor_get(v___x_4042_, 1);
                            leanh::lean_inc(v_a_4044_);
                            leanh::lean_dec_ref_known(v___x_4042_, 2);
                            v_ref_4045_ = leanh::lean_ctor_get(v___y_4034_, 5);
                            v___x_4046_ = l_Lean_SourceInfo_fromRef(v_ref_4045_, v___x_4041_);
                            v___x_4047_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4048_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4049_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4050_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4051_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            leanh::lean_inc_n(v___x_4046_, 15);
                            v___x_4052_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4052_, 0, v___x_4046_);
                            leanh::lean_ctor_set(v___x_4052_, 1, v___x_4051_);
                            v___x_4053_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4054_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_4054_, 0, v___x_4046_);
                            leanh::lean_ctor_set(v___x_4054_, 1, v___x_4048_);
                            leanh::lean_ctor_set(v___x_4054_, 2, v___x_4053_);
                            v___x_4055_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            leanh::lean_inc_ref_n(v___x_4054_, 4);
                            v___x_4056_ = l_Lean_Syntax_node2(
                                v___x_4046_,
                                v___x_4055_,
                                v___x_4054_,
                                v_a_4043_,
                            );
                            v___x_4057_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4056_);
                            v___x_4058_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4059_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4059_, 0, v___x_4046_);
                            leanh::lean_ctor_set(v___x_4059_, 1, v___x_4058_);
                            v___x_4060_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4061_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4063_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4063_, 0, v___x_4046_);
                            leanh::lean_ctor_set(v___x_4063_, 1, v___x_4062_);
                            v___x_4064_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4036_);
                            v___x_4065_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4064_);
                            v___x_4066_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4067_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4067_, 0, v___x_4046_);
                            leanh::lean_ctor_set(v___x_4067_, 1, v___x_4066_);
                            v___x_4068_ = l_Lean_Syntax_node4(
                                v___x_4046_,
                                v___x_4061_,
                                v___x_4063_,
                                v___x_4065_,
                                v___x_4067_,
                                v_body_4031_,
                            );
                            v___x_4069_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4068_);
                            v___x_4070_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4060_, v___x_4069_);
                            v___x_4071_ = l_Lean_Syntax_node7(
                                v___x_4046_,
                                v___x_4050_,
                                v___x_4052_,
                                v___x_4054_,
                                v___x_4054_,
                                v___x_4054_,
                                v___x_4057_,
                                v___x_4059_,
                                v___x_4070_,
                            );
                            v___x_4072_ = l_Lean_Syntax_node2(
                                v___x_4046_,
                                v___x_4049_,
                                v___x_4071_,
                                v___x_4054_,
                            );
                            v___x_4073_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4048_, v___x_4072_);
                            v___x_4074_ =
                                l_Lean_Syntax_node1(v___x_4046_, v___x_4047_, v___x_4073_);
                            v___y_3983_ = v_doElems_4038_;
                            v___y_3984_ = v___x_4037_;
                            v___y_3985_ = v_h_x3f_4033_;
                            v_x_3986_ = v_a_4043_;
                            v_body_3987_ = v___x_4074_;
                            v___y_3988_ = v___y_4034_;
                            v___y_3989_ = v_a_4044_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4037_);
                            leanh::lean_dec(v___x_4036_);
                            leanh::lean_dec(v_h_x3f_4033_);
                            leanh::lean_dec(v_body_4031_);
                            leanh::lean_dec_ref(v_decls_3981_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4075_ = leanh::lean_ctor_get(v___x_4042_, 0);
                            v_a_4076_ = leanh::lean_ctor_get(v___x_4042_, 1);
                            v_isSharedCheck_4083_ =
                                (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4083_ == 0 {
                                v___x_4078_ = v___x_4042_;
                                v_isShared_4079_ = v_isSharedCheck_4083_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4076_);
                                leanh::lean_inc(v_a_4075_);
                                leanh::lean_dec(v___x_4042_);
                                v___x_4078_ = leanh::lean_box(0);
                                v_isShared_4079_ = v_isSharedCheck_4083_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        v___x_4084_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4036_,
                                v___x_4039_,
                                v___y_4034_,
                                v___y_4035_,
                            );
                        leanh::lean_dec(v___x_4036_);
                        if leanh::lean_obj_tag(v___x_4084_) == 0 {
                            v_a_4085_ = leanh::lean_ctor_get(v___x_4084_, 0);
                            leanh::lean_inc(v_a_4085_);
                            v_a_4086_ = leanh::lean_ctor_get(v___x_4084_, 1);
                            leanh::lean_inc(v_a_4086_);
                            leanh::lean_dec_ref_known(v___x_4084_, 2);
                            v___y_3983_ = v_doElems_4038_;
                            v___y_3984_ = v___x_4037_;
                            v___y_3985_ = v_h_x3f_4033_;
                            v_x_3986_ = v_a_4085_;
                            v_body_3987_ = v_body_4031_;
                            v___y_3988_ = v___y_4034_;
                            v___y_3989_ = v_a_4086_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4037_);
                            leanh::lean_dec(v_h_x3f_4033_);
                            leanh::lean_dec(v_body_4031_);
                            leanh::lean_dec_ref(v_decls_3981_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4087_ = leanh::lean_ctor_get(v___x_4084_, 0);
                            v_a_4088_ = leanh::lean_ctor_get(v___x_4084_, 1);
                            v_isSharedCheck_4095_ =
                                (!leanh::lean_is_exclusive(v___x_4084_)) as u8;
                            if v_isSharedCheck_4095_ == 0 {
                                v___x_4090_ = v___x_4084_;
                                v_isShared_4091_ = v_isSharedCheck_4095_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4088_);
                                leanh::lean_inc(v_a_4087_);
                                leanh::lean_dec(v___x_4084_);
                                v___x_4090_ = leanh::lean_box(0);
                                v_isShared_4091_ = v_isSharedCheck_4095_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    v___y_3983_ = v_doElems_4038_;
                    v___y_3984_ = v___x_4037_;
                    v___y_3985_ = v_h_x3f_4033_;
                    v_x_3986_ = v___x_4036_;
                    v_body_3987_ = v_body_4031_;
                    v___y_3988_ = v___y_4034_;
                    v___y_3989_ = v___y_4035_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if v_isShared_4079_ == 0 {
                    v___x_4081_ = v___x_4078_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4082_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4082_, 1, v_a_4076_);
                    v___x_4081_ = v_reuseFailAlloc_4082_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4081_;
            }
            10 => {
                if v_isShared_4091_ == 0 {
                    v___x_4093_ = v___x_4090_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4094_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_a_4088_);
                    v___x_4093_ = v_reuseFailAlloc_4094_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4093_;
            }
            12 => {
                leanh::lean_inc_ref_n(v___y_4115_, 3);
                v___x_4118_ = l_Array_append___redArg(v___y_4115_, v___y_4117_);
                leanh::lean_dec_ref(v___y_4117_);
                leanh::lean_inc_n(v___y_4110_, 4);
                leanh::lean_inc_n(v___y_4108_, 10);
                v___x_4119_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4119_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4119_, 1, v___y_4110_);
                leanh::lean_ctor_set(v___x_4119_, 2, v___x_4118_);
                v___x_4120_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4121_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
                v___x_4122_ = l_Lean_Syntax_node4(
                    v___y_4108_,
                    v___x_4105_,
                    v___x_4119_,
                    v___y_4114_,
                    v___x_4121_,
                    v___y_4107_,
                );
                v___x_4123_ = l_Lean_Syntax_node1(v___y_4108_, v___y_4110_, v___x_4122_);
                v___x_4124_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76;
                v___x_4125_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4125_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                leanh::lean_inc_ref(v___x_4125_);
                v___x_4126_ = l_Lean_Syntax_node4(
                    v___y_4108_,
                    v___x_3940_,
                    v___y_4116_,
                    v___x_4123_,
                    v___x_4125_,
                    v___y_4112_,
                );
                v___x_4127_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4127_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4127_, 1, v___y_4110_);
                leanh::lean_ctor_set(v___x_4127_, 2, v___y_4115_);
                leanh::lean_inc(v___y_4113_);
                v___x_4128_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___y_4113_, v___x_4126_, v___x_4127_);
                v___x_4129_ = lean_array_push(v___y_4111_, v___x_4128_);
                v___x_4130_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4131_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4132_ = l_Array_append___redArg(v___y_4115_, v___x_4129_);
                leanh::lean_dec_ref(v___x_4129_);
                v___x_4133_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4133_, 0, v___y_4108_);
                leanh::lean_ctor_set(v___x_4133_, 1, v___y_4110_);
                leanh::lean_ctor_set(v___x_4133_, 2, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_node1(v___y_4108_, v___x_4131_, v___x_4133_);
                v___x_4135_ =
                    l_Lean_Syntax_node2(v___y_4108_, v___x_4130_, v___x_4125_, v___x_4134_);
                v___x_4136_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
                leanh::lean_ctor_set(v___x_4136_, 1, v___y_4109_);
                return v___x_4136_;
            }
            13 => {
                leanh::lean_inc_ref_n(v___y_4144_, 3);
                v___x_4149_ = l_Array_append___redArg(v___y_4144_, v___y_4148_);
                leanh::lean_dec_ref(v___y_4148_);
                leanh::lean_inc_n(v___y_4141_, 4);
                leanh::lean_inc_n(v___y_4145_, 10);
                v___x_4150_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4150_, 0, v___y_4145_);
                leanh::lean_ctor_set(v___x_4150_, 1, v___y_4141_);
                leanh::lean_ctor_set(v___x_4150_, 2, v___x_4149_);
                v___x_4151_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4152_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4152_, 0, v___y_4145_);
                leanh::lean_ctor_set(v___x_4152_, 1, v___x_4151_);
                v___x_4153_ = l_Lean_Syntax_node4(
                    v___y_4145_,
                    v___x_4105_,
                    v___x_4150_,
                    v___y_4139_,
                    v___x_4152_,
                    v___y_4140_,
                );
                v___x_4154_ = l_Lean_Syntax_node1(v___y_4145_, v___y_4141_, v___x_4153_);
                v___x_4155_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76;
                v___x_4156_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4156_, 0, v___y_4145_);
                leanh::lean_ctor_set(v___x_4156_, 1, v___x_4155_);
                leanh::lean_inc_ref(v___x_4156_);
                v___x_4157_ = l_Lean_Syntax_node4(
                    v___y_4145_,
                    v___x_3940_,
                    v___y_4143_,
                    v___x_4154_,
                    v___x_4156_,
                    v___y_4138_,
                );
                v___x_4158_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4158_, 0, v___y_4145_);
                leanh::lean_ctor_set(v___x_4158_, 1, v___y_4141_);
                leanh::lean_ctor_set(v___x_4158_, 2, v___y_4144_);
                leanh::lean_inc(v___y_4142_);
                v___x_4159_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___y_4142_, v___x_4157_, v___x_4158_);
                v___x_4160_ = lean_array_push(v___y_4146_, v___x_4159_);
                v___x_4161_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4162_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4163_ = l_Array_append___redArg(v___y_4144_, v___x_4160_);
                leanh::lean_dec_ref(v___x_4160_);
                v___x_4164_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4164_, 0, v___y_4145_);
                leanh::lean_ctor_set(v___x_4164_, 1, v___y_4141_);
                leanh::lean_ctor_set(v___x_4164_, 2, v___x_4163_);
                v___x_4165_ = l_Lean_Syntax_node1(v___y_4145_, v___x_4162_, v___x_4164_);
                v___x_4166_ =
                    l_Lean_Syntax_node2(v___y_4145_, v___x_4161_, v___x_4156_, v___x_4165_);
                v___x_4167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4167_, 0, v___x_4166_);
                leanh::lean_ctor_set(v___x_4167_, 1, v___y_4147_);
                return v___x_4167_;
            }
            14 => {
                v___x_4178_ = lean_array_get_size(v___y_4171_);
                v___x_4179_ = l_Array_toSubarray___redArg(v___y_4171_, v___x_3945_, v___x_4178_);
                leanh::lean_inc_ref(v___y_4172_);
                v___x_4180_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4180_, 0, v___y_4172_);
                leanh::lean_ctor_set(v___x_4180_, 1, v_body_4175_);
                v___x_4181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___y_4173_, v___x_4179_, v___x_4180_, v___y_4176_, v___y_4177_);
                if leanh::lean_obj_tag(v___x_4181_) == 0 {
                    v_a_4182_ = leanh::lean_ctor_get(v___x_4181_, 0);
                    leanh::lean_inc(v_a_4182_);
                    v_a_4183_ = leanh::lean_ctor_get(v___x_4181_, 1);
                    leanh::lean_inc(v_a_4183_);
                    leanh::lean_dec_ref_known(v___x_4181_, 2);
                    v_fst_4184_ = leanh::lean_ctor_get(v_a_4182_, 0);
                    v_snd_4185_ = leanh::lean_ctor_get(v_a_4182_, 1);
                    v_isSharedCheck_4204_ = (!leanh::lean_is_exclusive(v_a_4182_)) as u8;
                    if v_isSharedCheck_4204_ == 0 {
                        v___x_4187_ = v_a_4182_;
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4185_);
                        leanh::lean_inc(v_fst_4184_);
                        leanh::lean_dec(v_a_4182_);
                        v___x_4187_ = leanh::lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4204_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_4174_);
                    leanh::lean_dec(v___y_4170_);
                    leanh::lean_dec(v___y_4169_);
                    leanh::lean_dec(v_tk_3944_);
                    v_a_4205_ = leanh::lean_ctor_get(v___x_4181_, 0);
                    v_a_4206_ = leanh::lean_ctor_get(v___x_4181_, 1);
                    v_isSharedCheck_4213_ = (!leanh::lean_is_exclusive(v___x_4181_)) as u8;
                    if v_isSharedCheck_4213_ == 0 {
                        v___x_4208_ = v___x_4181_;
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4206_);
                        leanh::lean_inc(v_a_4205_);
                        leanh::lean_dec(v___x_4181_);
                        v___x_4208_ = leanh::lean_box(0);
                        v_isShared_4209_ = v_isSharedCheck_4213_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                v_ref_4189_ = leanh::lean_ctor_get(v___y_4176_, 5);
                v___x_4190_ = l_Lean_SourceInfo_fromRef(v_ref_4189_, v___y_4173_);
                v___x_4191_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4192_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                leanh::lean_dec(v_tk_3944_);
                v___x_4193_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4188_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4187_, 2);
                    leanh::lean_ctor_set(v___x_4187_, 1, v___x_4193_);
                    leanh::lean_ctor_set(v___x_4187_, 0, v___x_4192_);
                    v___x_4195_ = v___x_4187_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 1, v___x_4193_);
                    v___x_4195_ = v_reuseFailAlloc_4203_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4197_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if leanh::lean_obj_tag(v___y_4170_) == 1 {
                    v_val_4198_ = leanh::lean_ctor_get(v___y_4170_, 0);
                    leanh::lean_inc(v_val_4198_);
                    leanh::lean_dec_ref_known(v___y_4170_, 1);
                    v___x_4199_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    leanh::lean_inc(v___x_4190_);
                    v___x_4200_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4200_, 0, v___x_4190_);
                    leanh::lean_ctor_set(v___x_4200_, 1, v___x_4199_);
                    v___x_4201_ = l_Array_mkArray2___redArg(v_val_4198_, v___x_4200_);
                    v___y_4138_ = v_snd_4185_;
                    v___y_4139_ = v_x_4174_;
                    v___y_4140_ = v___y_4169_;
                    v___y_4141_ = v___x_4196_;
                    v___y_4142_ = v___x_4191_;
                    v___y_4143_ = v___x_4195_;
                    v___y_4144_ = v___x_4197_;
                    v___y_4145_ = v___x_4190_;
                    v___y_4146_ = v_fst_4184_;
                    v___y_4147_ = v_a_4183_;
                    v___y_4148_ = v___x_4201_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4170_);
                    v___x_4202_ = l_Lean_Elab_Do_expandDoFor___closed__8;
                    v___y_4138_ = v_snd_4185_;
                    v___y_4139_ = v_x_4174_;
                    v___y_4140_ = v___y_4169_;
                    v___y_4141_ = v___x_4196_;
                    v___y_4142_ = v___x_4191_;
                    v___y_4143_ = v___x_4195_;
                    v___y_4144_ = v___x_4197_;
                    v___y_4145_ = v___x_4190_;
                    v___y_4146_ = v_fst_4184_;
                    v___y_4147_ = v_a_4183_;
                    v___y_4148_ = v___x_4202_;
                    state = 13;
                    continue;
                }
            }
            17 => {
                if v_isShared_4209_ == 0 {
                    v___x_4211_ = v___x_4208_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_a_4206_);
                    v___x_4211_ = v_reuseFailAlloc_4212_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4211_;
            }
            19 => {
                v___x_4223_ = l_Lean_Syntax_getArg(v___y_4219_, v___x_3945_);
                v___x_4224_ = l_Lean_Syntax_getArg(v___y_4219_, v___y_4215_);
                leanh::lean_dec(v___y_4219_);
                v_doElems_4225_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4226_ = l_Lean_Syntax_isIdent(v___x_4223_);
                if v___x_4226_ == 0 {
                    v___x_4227_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    leanh::lean_inc(v___x_4223_);
                    v___x_4228_ = l_Lean_Syntax_isOfKind(v___x_4223_, v___x_4227_);
                    if v___x_4228_ == 0 {
                        v___x_4229_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4223_,
                                v___y_4218_,
                                v___y_4221_,
                                v___y_4222_,
                            );
                        if leanh::lean_obj_tag(v___x_4229_) == 0 {
                            v_a_4230_ = leanh::lean_ctor_get(v___x_4229_, 0);
                            leanh::lean_inc_n(v_a_4230_, 2);
                            v_a_4231_ = leanh::lean_ctor_get(v___x_4229_, 1);
                            leanh::lean_inc(v_a_4231_);
                            leanh::lean_dec_ref_known(v___x_4229_, 2);
                            v_ref_4232_ = leanh::lean_ctor_get(v___y_4221_, 5);
                            v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4232_, v___y_4218_);
                            v___x_4234_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4235_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4236_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4237_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4238_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            leanh::lean_inc_n(v___x_4233_, 15);
                            v___x_4239_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4239_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                            v___x_4240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4241_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_4241_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v___x_4241_, 1, v___x_4235_);
                            leanh::lean_ctor_set(v___x_4241_, 2, v___x_4240_);
                            v___x_4242_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            leanh::lean_inc_ref_n(v___x_4241_, 4);
                            v___x_4243_ = l_Lean_Syntax_node2(
                                v___x_4233_,
                                v___x_4242_,
                                v___x_4241_,
                                v_a_4230_,
                            );
                            v___x_4244_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4243_);
                            v___x_4245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4246_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4246_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                            v___x_4247_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4248_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4250_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4250_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v___x_4250_, 1, v___x_4249_);
                            v___x_4251_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4223_);
                            v___x_4252_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4251_);
                            v___x_4253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4254_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4254_, 0, v___x_4233_);
                            leanh::lean_ctor_set(v___x_4254_, 1, v___x_4253_);
                            v___x_4255_ = l_Lean_Syntax_node4(
                                v___x_4233_,
                                v___x_4248_,
                                v___x_4250_,
                                v___x_4252_,
                                v___x_4254_,
                                v___y_4217_,
                            );
                            v___x_4256_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4255_);
                            v___x_4257_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4247_, v___x_4256_);
                            v___x_4258_ = l_Lean_Syntax_node7(
                                v___x_4233_,
                                v___x_4237_,
                                v___x_4239_,
                                v___x_4241_,
                                v___x_4241_,
                                v___x_4241_,
                                v___x_4244_,
                                v___x_4246_,
                                v___x_4257_,
                            );
                            v___x_4259_ = l_Lean_Syntax_node2(
                                v___x_4233_,
                                v___x_4236_,
                                v___x_4258_,
                                v___x_4241_,
                            );
                            v___x_4260_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4235_, v___x_4259_);
                            v___x_4261_ =
                                l_Lean_Syntax_node1(v___x_4233_, v___x_4234_, v___x_4260_);
                            v___y_4169_ = v___x_4224_;
                            v___y_4170_ = v_h_x3f_4220_;
                            v___y_4171_ = v___y_4216_;
                            v___y_4172_ = v_doElems_4225_;
                            v___y_4173_ = v___y_4218_;
                            v_x_4174_ = v_a_4230_;
                            v_body_4175_ = v___x_4261_;
                            v___y_4176_ = v___y_4221_;
                            v___y_4177_ = v_a_4231_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4224_);
                            leanh::lean_dec(v___x_4223_);
                            leanh::lean_dec(v_h_x3f_4220_);
                            leanh::lean_dec(v___y_4217_);
                            leanh::lean_dec_ref(v___y_4216_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4262_ = leanh::lean_ctor_get(v___x_4229_, 0);
                            v_a_4263_ = leanh::lean_ctor_get(v___x_4229_, 1);
                            v_isSharedCheck_4270_ =
                                (!leanh::lean_is_exclusive(v___x_4229_)) as u8;
                            if v_isSharedCheck_4270_ == 0 {
                                v___x_4265_ = v___x_4229_;
                                v_isShared_4266_ = v_isSharedCheck_4270_;
                                state = 20;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4263_);
                                leanh::lean_inc(v_a_4262_);
                                leanh::lean_dec(v___x_4229_);
                                v___x_4265_ = leanh::lean_box(0);
                                v_isShared_4266_ = v_isSharedCheck_4270_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        v___x_4271_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4223_,
                                v___y_4218_,
                                v___y_4221_,
                                v___y_4222_,
                            );
                        leanh::lean_dec(v___x_4223_);
                        if leanh::lean_obj_tag(v___x_4271_) == 0 {
                            v_a_4272_ = leanh::lean_ctor_get(v___x_4271_, 0);
                            leanh::lean_inc(v_a_4272_);
                            v_a_4273_ = leanh::lean_ctor_get(v___x_4271_, 1);
                            leanh::lean_inc(v_a_4273_);
                            leanh::lean_dec_ref_known(v___x_4271_, 2);
                            v___y_4169_ = v___x_4224_;
                            v___y_4170_ = v_h_x3f_4220_;
                            v___y_4171_ = v___y_4216_;
                            v___y_4172_ = v_doElems_4225_;
                            v___y_4173_ = v___y_4218_;
                            v_x_4174_ = v_a_4272_;
                            v_body_4175_ = v___y_4217_;
                            v___y_4176_ = v___y_4221_;
                            v___y_4177_ = v_a_4273_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4224_);
                            leanh::lean_dec(v_h_x3f_4220_);
                            leanh::lean_dec(v___y_4217_);
                            leanh::lean_dec_ref(v___y_4216_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4274_ = leanh::lean_ctor_get(v___x_4271_, 0);
                            v_a_4275_ = leanh::lean_ctor_get(v___x_4271_, 1);
                            v_isSharedCheck_4282_ =
                                (!leanh::lean_is_exclusive(v___x_4271_)) as u8;
                            if v_isSharedCheck_4282_ == 0 {
                                v___x_4277_ = v___x_4271_;
                                v_isShared_4278_ = v_isSharedCheck_4282_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4275_);
                                leanh::lean_inc(v_a_4274_);
                                leanh::lean_dec(v___x_4271_);
                                v___x_4277_ = leanh::lean_box(0);
                                v_isShared_4278_ = v_isSharedCheck_4282_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                } else {
                    v___y_4169_ = v___x_4224_;
                    v___y_4170_ = v_h_x3f_4220_;
                    v___y_4171_ = v___y_4216_;
                    v___y_4172_ = v_doElems_4225_;
                    v___y_4173_ = v___y_4218_;
                    v_x_4174_ = v___x_4223_;
                    v_body_4175_ = v___y_4217_;
                    v___y_4176_ = v___y_4221_;
                    v___y_4177_ = v___y_4222_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                if v_isShared_4266_ == 0 {
                    v___x_4268_ = v___x_4265_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_a_4263_);
                    v___x_4268_ = v_reuseFailAlloc_4269_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4268_;
            }
            22 => {
                if v_isShared_4278_ == 0 {
                    v___x_4280_ = v___x_4277_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4281_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 1, v_a_4275_);
                    v___x_4280_ = v_reuseFailAlloc_4281_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4280_;
            }
            24 => {
                v___x_4286_ = l_Lean_Syntax_getArg(v___x_4104_, v___x_3945_);
                leanh::lean_dec(v___x_4104_);
                v___x_4287_ = l_Lean_Elab_Do_expandDoFor___closed__16;
                v___x_4288_ = l_Lean_Syntax_isOfKind(v___x_4286_, v___x_4287_);
                if v___x_4288_ == 0 {
                    v_decls_4289_ = l_Lean_Syntax_getArgs(v___x_3946_);
                    leanh::lean_dec(v___x_3946_);
                    v_decls_4290_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_decls_4289_);
                    leanh::lean_dec_ref(v_decls_4289_);
                    v___x_4291_ = leanh::lean_box(0);
                    v___x_4292_ = lean_array_get(v___x_4291_, v_decls_4290_, v___x_3943_);
                    leanh::lean_inc(v___x_4292_);
                    v___x_4293_ = l_Lean_Syntax_isOfKind(v___x_4292_, v___x_4105_);
                    if v___x_4293_ == 0 {
                        leanh::lean_dec(v___x_4292_);
                        leanh::lean_dec_ref(v_decls_4290_);
                        leanh::lean_dec(v_tk_3944_);
                        leanh::lean_dec(v_stx_3937_);
                        v___x_4294_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                        return v___x_4294_;
                    } else {
                        v___x_4295_ = leanh::lean_unsigned_to_nat(3);
                        v_body_4296_ = l_Lean_Syntax_getArg(v_stx_3937_, v___x_4295_);
                        leanh::lean_dec(v_stx_3937_);
                        v___x_4297_ = l_Lean_Syntax_getArg(v___x_4292_, v___x_3943_);
                        v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
                        if v___x_4298_ == 0 {
                            v___x_4299_ = leanh::lean_unsigned_to_nat(2);
                            leanh::lean_inc(v___x_4297_);
                            v___x_4300_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4299_);
                            if v___x_4300_ == 0 {
                                leanh::lean_dec(v___x_4297_);
                                leanh::lean_dec(v_body_4296_);
                                leanh::lean_dec(v___x_4292_);
                                leanh::lean_dec_ref(v_decls_4290_);
                                leanh::lean_dec(v_tk_3944_);
                                v___x_4301_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                                return v___x_4301_;
                            } else {
                                v_h_x3f_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_3943_);
                                leanh::lean_dec(v___x_4297_);
                                v___x_4303_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4303_, 0, v_h_x3f_4302_);
                                v___y_4215_ = v___x_4295_;
                                v___y_4216_ = v_decls_4290_;
                                v___y_4217_ = v_body_4296_;
                                v___y_4218_ = v___x_4288_;
                                v___y_4219_ = v___x_4292_;
                                v_h_x3f_4220_ = v___x_4303_;
                                v___y_4221_ = v___y_4284_;
                                v___y_4222_ = v___y_4285_;
                                state = 19;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_4297_);
                            v___x_4304_ = leanh::lean_box(0);
                            v___y_4215_ = v___x_4295_;
                            v___y_4216_ = v_decls_4290_;
                            v___y_4217_ = v_body_4296_;
                            v___y_4218_ = v___x_4288_;
                            v___y_4219_ = v___x_4292_;
                            v_h_x3f_4220_ = v___x_4304_;
                            v___y_4221_ = v___y_4284_;
                            v___y_4222_ = v___y_4285_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3946_);
                    leanh::lean_dec(v_tk_3944_);
                    leanh::lean_dec(v_stx_3937_);
                    v___x_4305_ = l_Lean_Macro_throwUnsupported___redArg(v___y_4285_);
                    return v___x_4305_;
                }
            }
            25 => {
                leanh::lean_inc_ref_n(v___y_4311_, 3);
                v___x_4318_ = l_Array_append___redArg(v___y_4311_, v___y_4317_);
                leanh::lean_dec_ref(v___y_4317_);
                leanh::lean_inc_n(v___y_4307_, 4);
                leanh::lean_inc_n(v___y_4308_, 10);
                v___x_4319_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4319_, 0, v___y_4308_);
                leanh::lean_ctor_set(v___x_4319_, 1, v___y_4307_);
                leanh::lean_ctor_set(v___x_4319_, 2, v___x_4318_);
                v___x_4320_ = l_Lean_Elab_Do_expandDoFor___closed__2;
                v___x_4321_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4321_, 0, v___y_4308_);
                leanh::lean_ctor_set(v___x_4321_, 1, v___x_4320_);
                v___x_4322_ = l_Lean_Syntax_node4(
                    v___y_4308_,
                    v___x_4105_,
                    v___x_4319_,
                    v___y_4314_,
                    v___x_4321_,
                    v___y_4315_,
                );
                v___x_4323_ = l_Lean_Syntax_node1(v___y_4308_, v___y_4307_, v___x_4322_);
                v___x_4324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__76;
                v___x_4325_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4325_, 0, v___y_4308_);
                leanh::lean_ctor_set(v___x_4325_, 1, v___x_4324_);
                leanh::lean_inc_ref(v___x_4325_);
                v___x_4326_ = l_Lean_Syntax_node4(
                    v___y_4308_,
                    v___x_3940_,
                    v___y_4312_,
                    v___x_4323_,
                    v___x_4325_,
                    v___y_4310_,
                );
                v___x_4327_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4327_, 0, v___y_4308_);
                leanh::lean_ctor_set(v___x_4327_, 1, v___y_4307_);
                leanh::lean_ctor_set(v___x_4327_, 2, v___y_4311_);
                leanh::lean_inc(v___y_4313_);
                v___x_4328_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___y_4313_, v___x_4326_, v___x_4327_);
                v___x_4329_ = lean_array_push(v___y_4309_, v___x_4328_);
                v___x_4330_ = l_Lean_Elab_Do_expandDoFor___closed__3;
                v___x_4331_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                v___x_4332_ = l_Array_append___redArg(v___y_4311_, v___x_4329_);
                leanh::lean_dec_ref(v___x_4329_);
                v___x_4333_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4333_, 0, v___y_4308_);
                leanh::lean_ctor_set(v___x_4333_, 1, v___y_4307_);
                leanh::lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                v___x_4334_ = l_Lean_Syntax_node1(v___y_4308_, v___x_4331_, v___x_4333_);
                v___x_4335_ =
                    l_Lean_Syntax_node2(v___y_4308_, v___x_4330_, v___x_4325_, v___x_4334_);
                v___x_4336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4336_, 0, v___x_4335_);
                leanh::lean_ctor_set(v___x_4336_, 1, v___y_4316_);
                return v___x_4336_;
            }
            26 => {
                v___x_4348_ = lean_array_get_size(v_decls_4339_);
                v___x_4349_ = l_Array_toSubarray___redArg(v_decls_4339_, v___x_3945_, v___x_4348_);
                leanh::lean_inc_ref(v___y_4343_);
                v___x_4350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4350_, 0, v___y_4343_);
                leanh::lean_ctor_set(v___x_4350_, 1, v_body_4345_);
                v___x_4351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4337_, v___x_4349_, v___x_4350_, v___y_4346_, v___y_4347_);
                if leanh::lean_obj_tag(v___x_4351_) == 0 {
                    v_a_4352_ = leanh::lean_ctor_get(v___x_4351_, 0);
                    leanh::lean_inc(v_a_4352_);
                    v_a_4353_ = leanh::lean_ctor_get(v___x_4351_, 1);
                    leanh::lean_inc(v_a_4353_);
                    leanh::lean_dec_ref_known(v___x_4351_, 2);
                    v_fst_4354_ = leanh::lean_ctor_get(v_a_4352_, 0);
                    v_snd_4355_ = leanh::lean_ctor_get(v_a_4352_, 1);
                    v_isSharedCheck_4374_ = (!leanh::lean_is_exclusive(v_a_4352_)) as u8;
                    if v_isSharedCheck_4374_ == 0 {
                        v___x_4357_ = v_a_4352_;
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4355_);
                        leanh::lean_inc(v_fst_4354_);
                        leanh::lean_dec(v_a_4352_);
                        v___x_4357_ = leanh::lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4374_;
                        state = 27;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_4344_);
                    leanh::lean_dec(v___y_4342_);
                    leanh::lean_dec(v___y_4341_);
                    leanh::lean_dec(v_tk_3944_);
                    v_a_4375_ = leanh::lean_ctor_get(v___x_4351_, 0);
                    v_a_4376_ = leanh::lean_ctor_get(v___x_4351_, 1);
                    v_isSharedCheck_4383_ = (!leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4383_ == 0 {
                        v___x_4378_ = v___x_4351_;
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4376_);
                        leanh::lean_inc(v_a_4375_);
                        leanh::lean_dec(v___x_4351_);
                        v___x_4378_ = leanh::lean_box(0);
                        v_isShared_4379_ = v_isSharedCheck_4383_;
                        state = 29;
                        continue;
                    }
                }
            }
            27 => {
                v_ref_4359_ = leanh::lean_ctor_get(v___y_4346_, 5);
                v___x_4360_ = l_Lean_SourceInfo_fromRef(v_ref_4359_, v___x_4337_);
                v___x_4361_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4362_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                leanh::lean_dec(v_tk_3944_);
                v___x_4363_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4358_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4357_, 2);
                    leanh::lean_ctor_set(v___x_4357_, 1, v___x_4363_);
                    leanh::lean_ctor_set(v___x_4357_, 0, v___x_4362_);
                    v___x_4365_ = v___x_4357_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4373_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 0, v___x_4362_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4373_, 1, v___x_4363_);
                    v___x_4365_ = v_reuseFailAlloc_4373_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4366_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4367_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if leanh::lean_obj_tag(v___y_4341_) == 1 {
                    v_val_4368_ = leanh::lean_ctor_get(v___y_4341_, 0);
                    leanh::lean_inc(v_val_4368_);
                    leanh::lean_dec_ref_known(v___y_4341_, 1);
                    v___x_4369_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    leanh::lean_inc(v___x_4360_);
                    v___x_4370_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4370_, 0, v___x_4360_);
                    leanh::lean_ctor_set(v___x_4370_, 1, v___x_4369_);
                    v___x_4371_ = l_Array_mkArray2___redArg(v_val_4368_, v___x_4370_);
                    v___y_4307_ = v___x_4366_;
                    v___y_4308_ = v___x_4360_;
                    v___y_4309_ = v_fst_4354_;
                    v___y_4310_ = v_snd_4355_;
                    v___y_4311_ = v___x_4367_;
                    v___y_4312_ = v___x_4365_;
                    v___y_4313_ = v___x_4361_;
                    v___y_4314_ = v_x_4344_;
                    v___y_4315_ = v___y_4342_;
                    v___y_4316_ = v_a_4353_;
                    v___y_4317_ = v___x_4371_;
                    state = 25;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4341_);
                    v___x_4372_ = l_Lean_Elab_Do_expandDoFor___closed__8;
                    v___y_4307_ = v___x_4366_;
                    v___y_4308_ = v___x_4360_;
                    v___y_4309_ = v_fst_4354_;
                    v___y_4310_ = v_snd_4355_;
                    v___y_4311_ = v___x_4367_;
                    v___y_4312_ = v___x_4365_;
                    v___y_4313_ = v___x_4361_;
                    v___y_4314_ = v_x_4344_;
                    v___y_4315_ = v___y_4342_;
                    v___y_4316_ = v_a_4353_;
                    v___y_4317_ = v___x_4372_;
                    state = 25;
                    continue;
                }
            }
            29 => {
                if v_isShared_4379_ == 0 {
                    v___x_4381_ = v___x_4378_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4375_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_a_4376_);
                    v___x_4381_ = v_reuseFailAlloc_4382_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4381_;
            }
            31 => {
                v___x_4394_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_3945_);
                v___x_4395_ = l_Lean_Syntax_getArg(v___x_4385_, v___x_4388_);
                leanh::lean_dec(v___x_4385_);
                v_doElems_4396_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4397_ = l_Lean_Syntax_isIdent(v___x_4394_);
                if v___x_4397_ == 0 {
                    v___x_4398_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    leanh::lean_inc(v___x_4394_);
                    v___x_4399_ = l_Lean_Syntax_isOfKind(v___x_4394_, v___x_4398_);
                    if v___x_4399_ == 0 {
                        v___x_4400_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4394_,
                                v___x_4399_,
                                v___y_4392_,
                                v___y_4393_,
                            );
                        if leanh::lean_obj_tag(v___x_4400_) == 0 {
                            v_a_4401_ = leanh::lean_ctor_get(v___x_4400_, 0);
                            leanh::lean_inc_n(v_a_4401_, 2);
                            v_a_4402_ = leanh::lean_ctor_get(v___x_4400_, 1);
                            leanh::lean_inc(v_a_4402_);
                            leanh::lean_dec_ref_known(v___x_4400_, 2);
                            v_ref_4403_ = leanh::lean_ctor_get(v___y_4392_, 5);
                            v___x_4404_ = l_Lean_SourceInfo_fromRef(v_ref_4403_, v___x_4399_);
                            v___x_4405_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4406_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4407_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4408_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4409_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            leanh::lean_inc_n(v___x_4404_, 15);
                            v___x_4410_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4410_, 0, v___x_4404_);
                            leanh::lean_ctor_set(v___x_4410_, 1, v___x_4409_);
                            v___x_4411_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4412_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_4412_, 0, v___x_4404_);
                            leanh::lean_ctor_set(v___x_4412_, 1, v___x_4406_);
                            leanh::lean_ctor_set(v___x_4412_, 2, v___x_4411_);
                            v___x_4413_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            leanh::lean_inc_ref_n(v___x_4412_, 4);
                            v___x_4414_ = l_Lean_Syntax_node2(
                                v___x_4404_,
                                v___x_4413_,
                                v___x_4412_,
                                v_a_4401_,
                            );
                            v___x_4415_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4414_);
                            v___x_4416_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4417_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4417_, 0, v___x_4404_);
                            leanh::lean_ctor_set(v___x_4417_, 1, v___x_4416_);
                            v___x_4418_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4419_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4421_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4421_, 0, v___x_4404_);
                            leanh::lean_ctor_set(v___x_4421_, 1, v___x_4420_);
                            v___x_4422_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4394_);
                            v___x_4423_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4422_);
                            v___x_4424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4425_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4425_, 0, v___x_4404_);
                            leanh::lean_ctor_set(v___x_4425_, 1, v___x_4424_);
                            v___x_4426_ = l_Lean_Syntax_node4(
                                v___x_4404_,
                                v___x_4419_,
                                v___x_4421_,
                                v___x_4423_,
                                v___x_4425_,
                                v_body_4389_,
                            );
                            v___x_4427_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4426_);
                            v___x_4428_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4418_, v___x_4427_);
                            v___x_4429_ = l_Lean_Syntax_node7(
                                v___x_4404_,
                                v___x_4408_,
                                v___x_4410_,
                                v___x_4412_,
                                v___x_4412_,
                                v___x_4412_,
                                v___x_4415_,
                                v___x_4417_,
                                v___x_4428_,
                            );
                            v___x_4430_ = l_Lean_Syntax_node2(
                                v___x_4404_,
                                v___x_4407_,
                                v___x_4429_,
                                v___x_4412_,
                            );
                            v___x_4431_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4406_, v___x_4430_);
                            v___x_4432_ =
                                l_Lean_Syntax_node1(v___x_4404_, v___x_4405_, v___x_4431_);
                            v___y_4341_ = v_h_x3f_4391_;
                            v___y_4342_ = v___x_4395_;
                            v___y_4343_ = v_doElems_4396_;
                            v_x_4344_ = v_a_4401_;
                            v_body_4345_ = v___x_4432_;
                            v___y_4346_ = v___y_4392_;
                            v___y_4347_ = v_a_4402_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4395_);
                            leanh::lean_dec(v___x_4394_);
                            leanh::lean_dec(v_h_x3f_4391_);
                            leanh::lean_dec(v_body_4389_);
                            leanh::lean_dec_ref(v_decls_4339_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4433_ = leanh::lean_ctor_get(v___x_4400_, 0);
                            v_a_4434_ = leanh::lean_ctor_get(v___x_4400_, 1);
                            v_isSharedCheck_4441_ =
                                (!leanh::lean_is_exclusive(v___x_4400_)) as u8;
                            if v_isSharedCheck_4441_ == 0 {
                                v___x_4436_ = v___x_4400_;
                                v_isShared_4437_ = v_isSharedCheck_4441_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4434_);
                                leanh::lean_inc(v_a_4433_);
                                leanh::lean_dec(v___x_4400_);
                                v___x_4436_ = leanh::lean_box(0);
                                v_isShared_4437_ = v_isSharedCheck_4441_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        v___x_4442_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4394_,
                                v___x_4397_,
                                v___y_4392_,
                                v___y_4393_,
                            );
                        leanh::lean_dec(v___x_4394_);
                        if leanh::lean_obj_tag(v___x_4442_) == 0 {
                            v_a_4443_ = leanh::lean_ctor_get(v___x_4442_, 0);
                            leanh::lean_inc(v_a_4443_);
                            v_a_4444_ = leanh::lean_ctor_get(v___x_4442_, 1);
                            leanh::lean_inc(v_a_4444_);
                            leanh::lean_dec_ref_known(v___x_4442_, 2);
                            v___y_4341_ = v_h_x3f_4391_;
                            v___y_4342_ = v___x_4395_;
                            v___y_4343_ = v_doElems_4396_;
                            v_x_4344_ = v_a_4443_;
                            v_body_4345_ = v_body_4389_;
                            v___y_4346_ = v___y_4392_;
                            v___y_4347_ = v_a_4444_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4395_);
                            leanh::lean_dec(v_h_x3f_4391_);
                            leanh::lean_dec(v_body_4389_);
                            leanh::lean_dec_ref(v_decls_4339_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4445_ = leanh::lean_ctor_get(v___x_4442_, 0);
                            v_a_4446_ = leanh::lean_ctor_get(v___x_4442_, 1);
                            v_isSharedCheck_4453_ =
                                (!leanh::lean_is_exclusive(v___x_4442_)) as u8;
                            if v_isSharedCheck_4453_ == 0 {
                                v___x_4448_ = v___x_4442_;
                                v_isShared_4449_ = v_isSharedCheck_4453_;
                                state = 34;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4446_);
                                leanh::lean_inc(v_a_4445_);
                                leanh::lean_dec(v___x_4442_);
                                v___x_4448_ = leanh::lean_box(0);
                                v_isShared_4449_ = v_isSharedCheck_4453_;
                                state = 34;
                                continue;
                            }
                        }
                    }
                } else {
                    v___y_4341_ = v_h_x3f_4391_;
                    v___y_4342_ = v___x_4395_;
                    v___y_4343_ = v_doElems_4396_;
                    v_x_4344_ = v___x_4394_;
                    v_body_4345_ = v_body_4389_;
                    v___y_4346_ = v___y_4392_;
                    v___y_4347_ = v___y_4393_;
                    state = 26;
                    continue;
                }
            }
            32 => {
                if v_isShared_4437_ == 0 {
                    v___x_4439_ = v___x_4436_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4440_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4440_, 1, v_a_4434_);
                    v___x_4439_ = v_reuseFailAlloc_4440_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4439_;
            }
            34 => {
                if v_isShared_4449_ == 0 {
                    v___x_4451_ = v___x_4448_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4452_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_a_4446_);
                    v___x_4451_ = v_reuseFailAlloc_4452_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4451_;
            }
            36 => {
                v___x_4476_ = lean_array_get_size(v_decls_4467_);
                v___x_4477_ = l_Array_toSubarray___redArg(v_decls_4467_, v___x_3945_, v___x_4476_);
                leanh::lean_inc_ref(v___y_4471_);
                v___x_4478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4478_, 0, v___y_4471_);
                leanh::lean_ctor_set(v___x_4478_, 1, v_body_4473_);
                v___x_4479_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(v___x_4465_, v___x_4477_, v___x_4478_, v___y_4474_, v___y_4475_);
                if leanh::lean_obj_tag(v___x_4479_) == 0 {
                    v_a_4480_ = leanh::lean_ctor_get(v___x_4479_, 0);
                    leanh::lean_inc(v_a_4480_);
                    v_a_4481_ = leanh::lean_ctor_get(v___x_4479_, 1);
                    leanh::lean_inc(v_a_4481_);
                    leanh::lean_dec_ref_known(v___x_4479_, 2);
                    v_fst_4482_ = leanh::lean_ctor_get(v_a_4480_, 0);
                    v_snd_4483_ = leanh::lean_ctor_get(v_a_4480_, 1);
                    v_isSharedCheck_4502_ = (!leanh::lean_is_exclusive(v_a_4480_)) as u8;
                    if v_isSharedCheck_4502_ == 0 {
                        v___x_4485_ = v_a_4480_;
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4483_);
                        leanh::lean_inc(v_fst_4482_);
                        leanh::lean_dec(v_a_4480_);
                        v___x_4485_ = leanh::lean_box(0);
                        v_isShared_4486_ = v_isSharedCheck_4502_;
                        state = 37;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_x_4472_);
                    leanh::lean_dec(v___y_4470_);
                    leanh::lean_dec(v___y_4469_);
                    leanh::lean_dec(v_tk_3944_);
                    v_a_4503_ = leanh::lean_ctor_get(v___x_4479_, 0);
                    v_a_4504_ = leanh::lean_ctor_get(v___x_4479_, 1);
                    v_isSharedCheck_4511_ = (!leanh::lean_is_exclusive(v___x_4479_)) as u8;
                    if v_isSharedCheck_4511_ == 0 {
                        v___x_4506_ = v___x_4479_;
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4504_);
                        leanh::lean_inc(v_a_4503_);
                        leanh::lean_dec(v___x_4479_);
                        v___x_4506_ = leanh::lean_box(0);
                        v_isShared_4507_ = v_isSharedCheck_4511_;
                        state = 39;
                        continue;
                    }
                }
            }
            37 => {
                v_ref_4487_ = leanh::lean_ctor_get(v___y_4474_, 5);
                v___x_4488_ = l_Lean_SourceInfo_fromRef(v_ref_4487_, v___x_4465_);
                v___x_4489_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                v___x_4490_ = l_Lean_SourceInfo_fromRef(v_tk_3944_, v___x_3941_);
                leanh::lean_dec(v_tk_3944_);
                v___x_4491_ = l_Lean_Elab_Do_expandDoFor___closed__6;
                if v_isShared_4486_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4485_, 2);
                    leanh::lean_ctor_set(v___x_4485_, 1, v___x_4491_);
                    leanh::lean_ctor_set(v___x_4485_, 0, v___x_4490_);
                    v___x_4493_ = v___x_4485_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v___x_4490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4491_);
                    v___x_4493_ = v_reuseFailAlloc_4501_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_4494_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                v___x_4495_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                if leanh::lean_obj_tag(v___y_4470_) == 1 {
                    v_val_4496_ = leanh::lean_ctor_get(v___y_4470_, 0);
                    leanh::lean_inc(v_val_4496_);
                    leanh::lean_dec_ref_known(v___y_4470_, 1);
                    v___x_4497_ = l_Lean_Elab_Do_expandDoFor___closed__7;
                    leanh::lean_inc(v___x_4488_);
                    v___x_4498_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4498_, 0, v___x_4488_);
                    leanh::lean_ctor_set(v___x_4498_, 1, v___x_4497_);
                    v___x_4499_ = l_Array_mkArray2___redArg(v_val_4496_, v___x_4498_);
                    v___y_4107_ = v___y_4469_;
                    v___y_4108_ = v___x_4488_;
                    v___y_4109_ = v_a_4481_;
                    v___y_4110_ = v___x_4494_;
                    v___y_4111_ = v_fst_4482_;
                    v___y_4112_ = v_snd_4483_;
                    v___y_4113_ = v___x_4489_;
                    v___y_4114_ = v_x_4472_;
                    v___y_4115_ = v___x_4495_;
                    v___y_4116_ = v___x_4493_;
                    v___y_4117_ = v___x_4499_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4470_);
                    v___x_4500_ = l_Lean_Elab_Do_expandDoFor___closed__8;
                    v___y_4107_ = v___y_4469_;
                    v___y_4108_ = v___x_4488_;
                    v___y_4109_ = v_a_4481_;
                    v___y_4110_ = v___x_4494_;
                    v___y_4111_ = v_fst_4482_;
                    v___y_4112_ = v_snd_4483_;
                    v___y_4113_ = v___x_4489_;
                    v___y_4114_ = v_x_4472_;
                    v___y_4115_ = v___x_4495_;
                    v___y_4116_ = v___x_4493_;
                    v___y_4117_ = v___x_4500_;
                    state = 12;
                    continue;
                }
            }
            39 => {
                if v_isShared_4507_ == 0 {
                    v___x_4509_ = v___x_4506_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4510_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4510_, 1, v_a_4504_);
                    v___x_4509_ = v_reuseFailAlloc_4510_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4509_;
            }
            41 => {
                v___x_4522_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_3945_);
                v___x_4523_ = l_Lean_Syntax_getArg(v___x_4513_, v___x_4516_);
                leanh::lean_dec(v___x_4513_);
                v_doElems_4524_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                v___x_4525_ = l_Lean_Syntax_isIdent(v___x_4522_);
                if v___x_4525_ == 0 {
                    v___x_4526_ = l_Lean_Elab_Do_expandDoFor___closed__10;
                    leanh::lean_inc(v___x_4522_);
                    v___x_4527_ = l_Lean_Syntax_isOfKind(v___x_4522_, v___x_4526_);
                    if v___x_4527_ == 0 {
                        v___x_4528_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4522_,
                                v___x_4527_,
                                v___y_4520_,
                                v___y_4521_,
                            );
                        if leanh::lean_obj_tag(v___x_4528_) == 0 {
                            v_a_4529_ = leanh::lean_ctor_get(v___x_4528_, 0);
                            leanh::lean_inc_n(v_a_4529_, 2);
                            v_a_4530_ = leanh::lean_ctor_get(v___x_4528_, 1);
                            leanh::lean_inc(v_a_4530_);
                            leanh::lean_dec_ref_known(v___x_4528_, 2);
                            v_ref_4531_ = leanh::lean_ctor_get(v___y_4520_, 5);
                            v___x_4532_ = l_Lean_SourceInfo_fromRef(v_ref_4531_, v___x_4527_);
                            v___x_4533_ = l_Lean_Elab_Do_expandDoFor___closed__4;
                            v___x_4534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__13;
                            v___x_4535_ = l_Lean_Elab_Do_expandDoFor___closed__5;
                            v___x_4536_ = l_Lean_Elab_Do_expandDoFor___closed__11;
                            v___x_4537_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__30;
                            leanh::lean_inc_n(v___x_4532_, 15);
                            v___x_4538_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4538_, 0, v___x_4532_);
                            leanh::lean_ctor_set(v___x_4538_, 1, v___x_4537_);
                            v___x_4539_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__23);
                            v___x_4540_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_4540_, 0, v___x_4532_);
                            leanh::lean_ctor_set(v___x_4540_, 1, v___x_4534_);
                            leanh::lean_ctor_set(v___x_4540_, 2, v___x_4539_);
                            v___x_4541_ = l_Lean_Elab_Do_expandDoFor___closed__12;
                            leanh::lean_inc_ref_n(v___x_4540_, 4);
                            v___x_4542_ = l_Lean_Syntax_node2(
                                v___x_4532_,
                                v___x_4541_,
                                v___x_4540_,
                                v_a_4529_,
                            );
                            v___x_4543_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4542_);
                            v___x_4544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__39;
                            v___x_4545_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4545_, 0, v___x_4532_);
                            leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                            v___x_4546_ = l_Lean_Elab_Do_expandDoFor___closed__13;
                            v___x_4547_ = l_Lean_Elab_Do_expandDoFor___closed__14;
                            v___x_4548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__42;
                            v___x_4549_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4549_, 0, v___x_4532_);
                            leanh::lean_ctor_set(v___x_4549_, 1, v___x_4548_);
                            v___x_4550_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4522_);
                            v___x_4551_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4550_);
                            v___x_4552_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__50;
                            v___x_4553_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4553_, 0, v___x_4532_);
                            leanh::lean_ctor_set(v___x_4553_, 1, v___x_4552_);
                            v___x_4554_ = l_Lean_Syntax_node4(
                                v___x_4532_,
                                v___x_4547_,
                                v___x_4549_,
                                v___x_4551_,
                                v___x_4553_,
                                v_body_4517_,
                            );
                            v___x_4555_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4554_);
                            v___x_4556_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4546_, v___x_4555_);
                            v___x_4557_ = l_Lean_Syntax_node7(
                                v___x_4532_,
                                v___x_4536_,
                                v___x_4538_,
                                v___x_4540_,
                                v___x_4540_,
                                v___x_4540_,
                                v___x_4543_,
                                v___x_4545_,
                                v___x_4556_,
                            );
                            v___x_4558_ = l_Lean_Syntax_node2(
                                v___x_4532_,
                                v___x_4535_,
                                v___x_4557_,
                                v___x_4540_,
                            );
                            v___x_4559_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4534_, v___x_4558_);
                            v___x_4560_ =
                                l_Lean_Syntax_node1(v___x_4532_, v___x_4533_, v___x_4559_);
                            v___y_4469_ = v___x_4523_;
                            v___y_4470_ = v_h_x3f_4519_;
                            v___y_4471_ = v_doElems_4524_;
                            v_x_4472_ = v_a_4529_;
                            v_body_4473_ = v___x_4560_;
                            v___y_4474_ = v___y_4520_;
                            v___y_4475_ = v_a_4530_;
                            state = 36;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4523_);
                            leanh::lean_dec(v___x_4522_);
                            leanh::lean_dec(v_h_x3f_4519_);
                            leanh::lean_dec(v_body_4517_);
                            leanh::lean_dec_ref(v_decls_4467_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4561_ = leanh::lean_ctor_get(v___x_4528_, 0);
                            v_a_4562_ = leanh::lean_ctor_get(v___x_4528_, 1);
                            v_isSharedCheck_4569_ =
                                (!leanh::lean_is_exclusive(v___x_4528_)) as u8;
                            if v_isSharedCheck_4569_ == 0 {
                                v___x_4564_ = v___x_4528_;
                                v_isShared_4565_ = v_isSharedCheck_4569_;
                                state = 42;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4562_);
                                leanh::lean_inc(v_a_4561_);
                                leanh::lean_dec(v___x_4528_);
                                v___x_4564_ = leanh::lean_box(0);
                                v_isShared_4565_ = v_isSharedCheck_4569_;
                                state = 42;
                                continue;
                            }
                        }
                    } else {
                        v___x_4570_ =
                            l_Lean_Elab_Term_mkFreshIdent___at___00Lean_Elab_Do_expandDoFor_spec__1(
                                v___x_4522_,
                                v___x_4525_,
                                v___y_4520_,
                                v___y_4521_,
                            );
                        leanh::lean_dec(v___x_4522_);
                        if leanh::lean_obj_tag(v___x_4570_) == 0 {
                            v_a_4571_ = leanh::lean_ctor_get(v___x_4570_, 0);
                            leanh::lean_inc(v_a_4571_);
                            v_a_4572_ = leanh::lean_ctor_get(v___x_4570_, 1);
                            leanh::lean_inc(v_a_4572_);
                            leanh::lean_dec_ref_known(v___x_4570_, 2);
                            v___y_4469_ = v___x_4523_;
                            v___y_4470_ = v_h_x3f_4519_;
                            v___y_4471_ = v_doElems_4524_;
                            v_x_4472_ = v_a_4571_;
                            v_body_4473_ = v_body_4517_;
                            v___y_4474_ = v___y_4520_;
                            v___y_4475_ = v_a_4572_;
                            state = 36;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4523_);
                            leanh::lean_dec(v_h_x3f_4519_);
                            leanh::lean_dec(v_body_4517_);
                            leanh::lean_dec_ref(v_decls_4467_);
                            leanh::lean_dec(v_tk_3944_);
                            v_a_4573_ = leanh::lean_ctor_get(v___x_4570_, 0);
                            v_a_4574_ = leanh::lean_ctor_get(v___x_4570_, 1);
                            v_isSharedCheck_4581_ =
                                (!leanh::lean_is_exclusive(v___x_4570_)) as u8;
                            if v_isSharedCheck_4581_ == 0 {
                                v___x_4576_ = v___x_4570_;
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 44;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4574_);
                                leanh::lean_inc(v_a_4573_);
                                leanh::lean_dec(v___x_4570_);
                                v___x_4576_ = leanh::lean_box(0);
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 44;
                                continue;
                            }
                        }
                    }
                } else {
                    v___y_4469_ = v___x_4523_;
                    v___y_4470_ = v_h_x3f_4519_;
                    v___y_4471_ = v_doElems_4524_;
                    v_x_4472_ = v___x_4522_;
                    v_body_4473_ = v_body_4517_;
                    v___y_4474_ = v___y_4520_;
                    v___y_4475_ = v___y_4521_;
                    state = 36;
                    continue;
                }
            }
            42 => {
                if v_isShared_4565_ == 0 {
                    v___x_4567_ = v___x_4564_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4568_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4568_, 1, v_a_4562_);
                    v___x_4567_ = v_reuseFailAlloc_4568_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4567_;
            }
            44 => {
                if v_isShared_4577_ == 0 {
                    v___x_4579_ = v___x_4576_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4580_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 1, v_a_4574_);
                    v___x_4579_ = v_reuseFailAlloc_4580_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_expandDoFor___boxed(
    mut v_stx_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lean_Elab_Do_expandDoFor(v_stx_4589_, v_a_4590_, v_a_4591_);
    leanh::lean_dec_ref(v_a_4590_);
    return v_res_4592_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(
    mut v___x_4593_: u8,
    mut v_inst_4594_: *mut leanh::LeanObject,
    mut v_R_4595_: *mut leanh::LeanObject,
    mut v_a_4596_: *mut leanh::LeanObject,
    mut v_b_4597_: *mut leanh::LeanObject,
    mut v_c_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg(
        v___x_4593_,
        v_a_4596_,
        v_b_4597_,
        v___y_4599_,
        v___y_4600_,
    );
    return v___x_4601_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___boxed(
    mut v___x_4602_: *mut leanh::LeanObject,
    mut v_inst_4603_: *mut leanh::LeanObject,
    mut v_R_4604_: *mut leanh::LeanObject,
    mut v_a_4605_: *mut leanh::LeanObject,
    mut v_b_4606_: *mut leanh::LeanObject,
    mut v_c_4607_: *mut leanh::LeanObject,
    mut v___y_4608_: *mut leanh::LeanObject,
    mut v___y_4609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_148624__boxed_4610_: u8 = 0;
    let mut v_res_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_148624__boxed_4610_ = (leanh::lean_unbox(v___x_4602_) as u8);
    v_res_4611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0(
        v___x_148624__boxed_4610_,
        v_inst_4603_,
        v_R_4604_,
        v_a_4605_,
        v_b_4606_,
        v_c_4607_,
        v___y_4608_,
        v___y_4609_,
    );
    leanh::lean_dec_ref(v___y_4608_);
    return v_res_4611_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1()
-> *mut leanh::LeanObject {
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4619_ = l_Lean_Elab_macroAttribute;
    v___x_4620_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_4621_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___closed__1;
    v___x_4622_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_expandDoFor___boxed as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_4623_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4619_,
        v___x_4620_,
        v___x_4621_,
        v___x_4622_,
    );
    return v___x_4623_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1___boxed(
    mut v_a_4624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4625_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    return v_res_4625_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = leanh::lean_box(0);
    v___x_4627_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4628_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4628_, 0, v___x_4627_);
    leanh::lean_ctor_set(v___x_4628_, 1, v___x_4626_);
    return v___x_4628_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4630_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___closed__0);
    v___x_4631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4631_, 0, v___x_4630_);
    return v___x_4631_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg___boxed(
    mut v___y_4632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v_res_4633_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(
    mut v_00_u03b1_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
    mut v___y_4638_: *mut leanh::LeanObject,
    mut v___y_4639_: *mut leanh::LeanObject,
    mut v___y_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
    return v___x_4643_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___boxed(
    mut v_00_u03b1_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0(
        v_00_u03b1_4644_,
        v___y_4645_,
        v___y_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
        v___y_4651_,
    );
    leanh::lean_dec(v___y_4651_);
    leanh::lean_dec_ref(v___y_4650_);
    leanh::lean_dec(v___y_4649_);
    leanh::lean_dec_ref(v___y_4648_);
    leanh::lean_dec(v___y_4647_);
    leanh::lean_dec_ref(v___y_4646_);
    leanh::lean_dec_ref(v___y_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(
    mut v_k_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v_b_4658_: *mut leanh::LeanObject,
    mut v___y_4659_: *mut leanh::LeanObject,
    mut v___y_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
    mut v___y_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4662_);
    leanh::lean_inc_ref(v___y_4661_);
    leanh::lean_inc(v___y_4660_);
    leanh::lean_inc_ref(v___y_4659_);
    leanh::lean_inc(v___y_4657_);
    leanh::lean_inc_ref(v___y_4656_);
    leanh::lean_inc_ref(v___y_4655_);
    v___x_4664_ = leanh::lean_apply_9(
        v_k_4654_,
        v_b_4658_,
        v___y_4655_,
        v___y_4656_,
        v___y_4657_,
        v___y_4659_,
        v___y_4660_,
        v___y_4661_,
        v___y_4662_,
        leanh::lean_box(0),
    );
    return v___x_4664_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed(
    mut v_k_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
    mut v___y_4668_: *mut leanh::LeanObject,
    mut v_b_4669_: *mut leanh::LeanObject,
    mut v___y_4670_: *mut leanh::LeanObject,
    mut v___y_4671_: *mut leanh::LeanObject,
    mut v___y_4672_: *mut leanh::LeanObject,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4675_ =
        l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0(
            v_k_4665_,
            v___y_4666_,
            v___y_4667_,
            v___y_4668_,
            v_b_4669_,
            v___y_4670_,
            v___y_4671_,
            v___y_4672_,
            v___y_4673_,
        );
    leanh::lean_dec(v___y_4673_);
    leanh::lean_dec_ref(v___y_4672_);
    leanh::lean_dec(v___y_4671_);
    leanh::lean_dec_ref(v___y_4670_);
    leanh::lean_dec(v___y_4668_);
    leanh::lean_dec_ref(v___y_4667_);
    leanh::lean_dec_ref(v___y_4666_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
    mut v_name_4676_: *mut leanh::LeanObject,
    mut v_bi_4677_: u8,
    mut v_type_4678_: *mut leanh::LeanObject,
    mut v_k_4679_: *mut leanh::LeanObject,
    mut v_kind_4680_: u8,
    mut v___y_4681_: *mut leanh::LeanObject,
    mut v___y_4682_: *mut leanh::LeanObject,
    mut v___y_4683_: *mut leanh::LeanObject,
    mut v___y_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4694_: u8 = 0;
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4683_);
                leanh::lean_inc_ref(v___y_4682_);
                leanh::lean_inc_ref(v___y_4681_);
                v___f_4689_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                leanh::lean_closure_set(v___f_4689_, 0, v_k_4679_);
                leanh::lean_closure_set(v___f_4689_, 1, v___y_4681_);
                leanh::lean_closure_set(v___f_4689_, 2, v___y_4682_);
                leanh::lean_closure_set(v___f_4689_, 3, v___y_4683_);
                v___x_4690_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_4676_,
                    v_bi_4677_,
                    v_type_4678_,
                    v___f_4689_,
                    v_kind_4680_,
                    v___y_4684_,
                    v___y_4685_,
                    v___y_4686_,
                    v___y_4687_,
                );
                if leanh::lean_obj_tag(v___x_4690_) == 0 {
                    return v___x_4690_;
                } else {
                    v_a_4691_ = leanh::lean_ctor_get(v___x_4690_, 0);
                    v_isSharedCheck_4698_ = (!leanh::lean_is_exclusive(v___x_4690_)) as u8;
                    if v_isSharedCheck_4698_ == 0 {
                        v___x_4693_ = v___x_4690_;
                        v_isShared_4694_ = v_isSharedCheck_4698_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4691_);
                        leanh::lean_dec(v___x_4690_);
                        v___x_4693_ = leanh::lean_box(0);
                        v_isShared_4694_ = v_isSharedCheck_4698_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4694_ == 0 {
                    v___x_4696_ = v___x_4693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4697_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4697_, 0, v_a_4691_);
                    v___x_4696_ = v_reuseFailAlloc_4697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg___boxed(
    mut v_name_4699_: *mut leanh::LeanObject,
    mut v_bi_4700_: *mut leanh::LeanObject,
    mut v_type_4701_: *mut leanh::LeanObject,
    mut v_k_4702_: *mut leanh::LeanObject,
    mut v_kind_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
    mut v___y_4706_: *mut leanh::LeanObject,
    mut v___y_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4712_: u8 = 0;
    let mut v_kind_boxed_4713_: u8 = 0;
    let mut v_res_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4712_ = (leanh::lean_unbox(v_bi_4700_) as u8);
    v_kind_boxed_4713_ = (leanh::lean_unbox(v_kind_4703_) as u8);
    v_res_4714_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
        v_name_4699_,
        v_bi_boxed_4712_,
        v_type_4701_,
        v_k_4702_,
        v_kind_boxed_4713_,
        v___y_4704_,
        v___y_4705_,
        v___y_4706_,
        v___y_4707_,
        v___y_4708_,
        v___y_4709_,
        v___y_4710_,
    );
    leanh::lean_dec(v___y_4710_);
    leanh::lean_dec_ref(v___y_4709_);
    leanh::lean_dec(v___y_4708_);
    leanh::lean_dec_ref(v___y_4707_);
    leanh::lean_dec(v___y_4706_);
    leanh::lean_dec_ref(v___y_4705_);
    leanh::lean_dec_ref(v___y_4704_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(
    mut v_00_u03b1_4715_: *mut leanh::LeanObject,
    mut v_name_4716_: *mut leanh::LeanObject,
    mut v_bi_4717_: u8,
    mut v_type_4718_: *mut leanh::LeanObject,
    mut v_k_4719_: *mut leanh::LeanObject,
    mut v_kind_4720_: u8,
    mut v___y_4721_: *mut leanh::LeanObject,
    mut v___y_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4729_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
        v_name_4716_,
        v_bi_4717_,
        v_type_4718_,
        v_k_4719_,
        v_kind_4720_,
        v___y_4721_,
        v___y_4722_,
        v___y_4723_,
        v___y_4724_,
        v___y_4725_,
        v___y_4726_,
        v___y_4727_,
    );
    return v___x_4729_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___boxed(
    mut v_00_u03b1_4730_: *mut leanh::LeanObject,
    mut v_name_4731_: *mut leanh::LeanObject,
    mut v_bi_4732_: *mut leanh::LeanObject,
    mut v_type_4733_: *mut leanh::LeanObject,
    mut v_k_4734_: *mut leanh::LeanObject,
    mut v_kind_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
    mut v___y_4743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4744_: u8 = 0;
    let mut v_kind_boxed_4745_: u8 = 0;
    let mut v_res_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4744_ = (leanh::lean_unbox(v_bi_4732_) as u8);
    v_kind_boxed_4745_ = (leanh::lean_unbox(v_kind_4735_) as u8);
    v_res_4746_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3(
        v_00_u03b1_4730_,
        v_name_4731_,
        v_bi_boxed_4744_,
        v_type_4733_,
        v_k_4734_,
        v_kind_boxed_4745_,
        v___y_4736_,
        v___y_4737_,
        v___y_4738_,
        v___y_4739_,
        v___y_4740_,
        v___y_4741_,
        v___y_4742_,
    );
    leanh::lean_dec(v___y_4742_);
    leanh::lean_dec_ref(v___y_4741_);
    leanh::lean_dec(v___y_4740_);
    leanh::lean_dec_ref(v___y_4739_);
    leanh::lean_dec(v___y_4738_);
    leanh::lean_dec_ref(v___y_4737_);
    leanh::lean_dec_ref(v___y_4736_);
    return v_res_4746_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0(
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_x_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
    mut v___y_4755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4757_, 0, v_a_4747_);
    return v___x_4757_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__0___boxed(
    mut v_a_4758_: *mut leanh::LeanObject,
    mut v_x_4759_: *mut leanh::LeanObject,
    mut v___y_4760_: *mut leanh::LeanObject,
    mut v___y_4761_: *mut leanh::LeanObject,
    mut v___y_4762_: *mut leanh::LeanObject,
    mut v___y_4763_: *mut leanh::LeanObject,
    mut v___y_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v___y_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4768_ = l_Lean_Elab_Do_elabDoFor___lam__0(
        v_a_4758_,
        v_x_4759_,
        v___y_4760_,
        v___y_4761_,
        v___y_4762_,
        v___y_4763_,
        v___y_4764_,
        v___y_4765_,
        v___y_4766_,
    );
    leanh::lean_dec(v___y_4766_);
    leanh::lean_dec_ref(v___y_4765_);
    leanh::lean_dec(v___y_4764_);
    leanh::lean_dec_ref(v___y_4763_);
    leanh::lean_dec(v___y_4762_);
    leanh::lean_dec_ref(v___y_4761_);
    leanh::lean_dec_ref(v___y_4760_);
    leanh::lean_dec_ref(v_x_4759_);
    return v_res_4768_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2(
    mut v_x_4769_: *mut leanh::LeanObject,
    mut v___f_4770_: *mut leanh::LeanObject,
    mut v___x_4771_: *mut leanh::LeanObject,
    mut v_x_4772_: *mut leanh::LeanObject,
    mut v_x_4773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4774_ = l_Lean_TSyntax_getId(v_x_4769_);
    v___x_4775_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4775_, 0, v___x_4774_);
    leanh::lean_ctor_set(v___x_4775_, 1, v___f_4770_);
    v___x_4776_ = lean_mk_empty_array_with_capacity(v___x_4771_);
    v___x_4777_ = lean_array_push(v___x_4776_, v___x_4775_);
    return v___x_4777_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__2___boxed(
    mut v_x_4778_: *mut leanh::LeanObject,
    mut v___f_4779_: *mut leanh::LeanObject,
    mut v___x_4780_: *mut leanh::LeanObject,
    mut v_x_4781_: *mut leanh::LeanObject,
    mut v_x_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Elab_Do_elabDoFor___lam__2(
        v_x_4778_,
        v___f_4779_,
        v___x_4780_,
        v_x_4781_,
        v_x_4782_,
    );
    leanh::lean_dec(v_x_4782_);
    leanh::lean_dec(v_x_4781_);
    leanh::lean_dec(v___x_4780_);
    leanh::lean_dec(v_x_4778_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1(
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v___x_4785_: *mut leanh::LeanObject,
    mut v___x_4786_: u8,
    mut v_r_4787_: *mut leanh::LeanObject,
    mut v___y_4788_: *mut leanh::LeanObject,
    mut v___y_4789_: *mut leanh::LeanObject,
    mut v___y_4790_: *mut leanh::LeanObject,
    mut v___y_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
    mut v___y_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_k_4796_ = leanh::lean_ctor_get(v_a_4784_, 1);
    leanh::lean_inc_ref(v_k_4796_);
    leanh::lean_dec_ref(v_a_4784_);
    leanh::lean_inc(v___y_4794_);
    leanh::lean_inc_ref(v___y_4793_);
    leanh::lean_inc(v___y_4792_);
    leanh::lean_inc_ref(v___y_4791_);
    leanh::lean_inc(v___y_4790_);
    leanh::lean_inc_ref(v___y_4789_);
    leanh::lean_inc_ref(v___y_4788_);
    leanh::lean_inc_ref(v_r_4787_);
    v___x_4797_ = leanh::lean_apply_9(
        v_k_4796_,
        v_r_4787_,
        v___y_4788_,
        v___y_4789_,
        v___y_4790_,
        v___y_4791_,
        v___y_4792_,
        v___y_4793_,
        v___y_4794_,
        leanh::lean_box(0),
    );
    if leanh::lean_obj_tag(v___x_4797_) == 0 {
        let mut v_a_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4801_: u8 = 0;
        let mut v___x_4802_: u8 = 0;
        let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4798_ = leanh::lean_ctor_get(v___x_4797_, 0);
        leanh::lean_inc(v_a_4798_);
        leanh::lean_dec_ref_known(v___x_4797_, 1);
        v___x_4799_ = lean_mk_empty_array_with_capacity(v___x_4785_);
        v___x_4800_ = lean_array_push(v___x_4799_, v_r_4787_);
        v___x_4801_ = 0;
        v___x_4802_ = 1;
        v___x_4803_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4800_,
            v_a_4798_,
            v___x_4801_,
            v___x_4786_,
            v___x_4801_,
            v___x_4786_,
            v___x_4802_,
            v___y_4791_,
            v___y_4792_,
            v___y_4793_,
            v___y_4794_,
        );
        leanh::lean_dec_ref(v___x_4800_);
        return v___x_4803_;
    } else {
        leanh::lean_dec_ref(v_r_4787_);
        return v___x_4797_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__1___boxed(
    mut v_a_4804_: *mut leanh::LeanObject,
    mut v___x_4805_: *mut leanh::LeanObject,
    mut v___x_4806_: *mut leanh::LeanObject,
    mut v_r_4807_: *mut leanh::LeanObject,
    mut v___y_4808_: *mut leanh::LeanObject,
    mut v___y_4809_: *mut leanh::LeanObject,
    mut v___y_4810_: *mut leanh::LeanObject,
    mut v___y_4811_: *mut leanh::LeanObject,
    mut v___y_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_71074__boxed_4816_: u8 = 0;
    let mut v_res_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_71074__boxed_4816_ = (leanh::lean_unbox(v___x_4806_) as u8);
    v_res_4817_ = l_Lean_Elab_Do_elabDoFor___lam__1(
        v_a_4804_,
        v___x_4805_,
        v___x_71074__boxed_4816_,
        v_r_4807_,
        v___y_4808_,
        v___y_4809_,
        v___y_4810_,
        v___y_4811_,
        v___y_4812_,
        v___y_4813_,
        v___y_4814_,
    );
    leanh::lean_dec(v___y_4814_);
    leanh::lean_dec_ref(v___y_4813_);
    leanh::lean_dec(v___y_4812_);
    leanh::lean_dec_ref(v___y_4811_);
    leanh::lean_dec(v___y_4810_);
    leanh::lean_dec_ref(v___y_4809_);
    leanh::lean_dec_ref(v___y_4808_);
    leanh::lean_dec(v___x_4805_);
    return v_res_4817_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(
    mut v___x_4818_: *mut leanh::LeanObject,
    mut v_as_4819_: *mut leanh::LeanObject,
    mut v_sz_4820_: usize,
    mut v_i_4821_: usize,
    mut v_b_4822_: *mut leanh::LeanObject,
    mut v___y_4823_: *mut leanh::LeanObject,
    mut v___y_4824_: *mut leanh::LeanObject,
    mut v___y_4825_: *mut leanh::LeanObject,
    mut v___y_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: usize = 0;
    let mut v___x_4848_: usize = 0;
    let mut v_a_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4853_: u8 = 0;
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4857_: u8 = 0;
    let mut v_a_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_a_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4869_: u8 = 0;
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4873_: u8 = 0;
    let mut v_a_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4877_: u8 = 0;
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4830_ = lean_usize_dec_lt(v_i_4821_, v_sz_4820_);
                if v___x_4830_ == 0 {
                    leanh::lean_dec_ref(v___x_4818_);
                    v___x_4831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4831_, 0, v_b_4822_);
                    return v___x_4831_;
                } else {
                    v_a_4832_ = lean_array_uget_borrowed(v_as_4819_, v_i_4821_);
                    v___x_4833_ = l_Lean_TSyntax_getId(v_a_4832_);
                    v___x_4834_ = l_Lean_Meta_getLocalDeclFromUserName(
                        v___x_4833_,
                        v___y_4825_,
                        v___y_4826_,
                        v___y_4827_,
                        v___y_4828_,
                    );
                    if leanh::lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = leanh::lean_ctor_get(v___x_4834_, 0);
                        leanh::lean_inc_n(v_a_4835_, 2);
                        leanh::lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4836_ = l_Lean_LocalDecl_toExpr(v_a_4835_);
                        v___x_4837_ = leanh::lean_box(0);
                        v___x_4838_ = leanh::lean_box(0);
                        v___x_4839_ = 0;
                        leanh::lean_inc_ref(v___x_4836_);
                        leanh::lean_inc(v_a_4832_);
                        v___x_4840_ = l_Lean_Elab_Term_addTermInfo_x27(
                            v_a_4832_,
                            v___x_4836_,
                            v___x_4837_,
                            v___x_4837_,
                            v___x_4838_,
                            v___x_4839_,
                            v___x_4839_,
                            v___y_4823_,
                            v___y_4824_,
                            v___y_4825_,
                            v___y_4826_,
                            v___y_4827_,
                            v___y_4828_,
                        );
                        if leanh::lean_obj_tag(v___x_4840_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4840_, 1);
                            v___x_4841_ = l_Lean_LocalDecl_type(v_a_4835_);
                            leanh::lean_dec(v_a_4835_);
                            v___x_4842_ = l_Lean_Meta_getDecLevel(
                                v___x_4841_,
                                v___y_4825_,
                                v___y_4826_,
                                v___y_4827_,
                                v___y_4828_,
                            );
                            if leanh::lean_obj_tag(v___x_4842_) == 0 {
                                v_a_4843_ = leanh::lean_ctor_get(v___x_4842_, 0);
                                leanh::lean_inc(v_a_4843_);
                                leanh::lean_dec_ref_known(v___x_4842_, 1);
                                v_u_4844_ = leanh::lean_ctor_get(v___x_4818_, 1);
                                leanh::lean_inc(v_u_4844_);
                                v___x_4845_ = l_Lean_Meta_isLevelDefEq(
                                    v_a_4843_,
                                    v_u_4844_,
                                    v___y_4825_,
                                    v___y_4826_,
                                    v___y_4827_,
                                    v___y_4828_,
                                );
                                if leanh::lean_obj_tag(v___x_4845_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4845_, 1);
                                    v___x_4846_ = lean_array_push(v_b_4822_, v___x_4836_);
                                    v___x_4847_ = 1usize;
                                    v___x_4848_ = lean_usize_add(v_i_4821_, v___x_4847_);
                                    v_i_4821_ = v___x_4848_;
                                    v_b_4822_ = v___x_4846_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v___x_4836_);
                                    leanh::lean_dec_ref(v_b_4822_);
                                    leanh::lean_dec_ref(v___x_4818_);
                                    v_a_4850_ = leanh::lean_ctor_get(v___x_4845_, 0);
                                    v_isSharedCheck_4857_ =
                                        (!leanh::lean_is_exclusive(v___x_4845_)) as u8;
                                    if v_isSharedCheck_4857_ == 0 {
                                        v___x_4852_ = v___x_4845_;
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4850_);
                                        leanh::lean_dec(v___x_4845_);
                                        v___x_4852_ = leanh::lean_box(0);
                                        v_isShared_4853_ = v_isSharedCheck_4857_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4836_);
                                leanh::lean_dec_ref(v_b_4822_);
                                leanh::lean_dec_ref(v___x_4818_);
                                v_a_4858_ = leanh::lean_ctor_get(v___x_4842_, 0);
                                v_isSharedCheck_4865_ =
                                    (!leanh::lean_is_exclusive(v___x_4842_)) as u8;
                                if v_isSharedCheck_4865_ == 0 {
                                    v___x_4860_ = v___x_4842_;
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4858_);
                                    leanh::lean_dec(v___x_4842_);
                                    v___x_4860_ = leanh::lean_box(0);
                                    v_isShared_4861_ = v_isSharedCheck_4865_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4836_);
                            leanh::lean_dec(v_a_4835_);
                            leanh::lean_dec_ref(v_b_4822_);
                            leanh::lean_dec_ref(v___x_4818_);
                            v_a_4866_ = leanh::lean_ctor_get(v___x_4840_, 0);
                            v_isSharedCheck_4873_ =
                                (!leanh::lean_is_exclusive(v___x_4840_)) as u8;
                            if v_isSharedCheck_4873_ == 0 {
                                v___x_4868_ = v___x_4840_;
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4866_);
                                leanh::lean_dec(v___x_4840_);
                                v___x_4868_ = leanh::lean_box(0);
                                v_isShared_4869_ = v_isSharedCheck_4873_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_4822_);
                        leanh::lean_dec_ref(v___x_4818_);
                        v_a_4874_ = leanh::lean_ctor_get(v___x_4834_, 0);
                        v_isSharedCheck_4881_ =
                            (!leanh::lean_is_exclusive(v___x_4834_)) as u8;
                        if v_isSharedCheck_4881_ == 0 {
                            v___x_4876_ = v___x_4834_;
                            v_isShared_4877_ = v_isSharedCheck_4881_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4874_);
                            leanh::lean_dec(v___x_4834_);
                            v___x_4876_ = leanh::lean_box(0);
                            v_isShared_4877_ = v_isSharedCheck_4881_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4853_ == 0 {
                    v___x_4855_ = v___x_4852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4856_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
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
                    v_reuseFailAlloc_4864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
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
                    v_reuseFailAlloc_4872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4866_);
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
                    v_reuseFailAlloc_4880_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4874_);
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
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1___boxed(
    mut v___x_4882_: *mut leanh::LeanObject,
    mut v_as_4883_: *mut leanh::LeanObject,
    mut v_sz_4884_: *mut leanh::LeanObject,
    mut v_i_4885_: *mut leanh::LeanObject,
    mut v_b_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
    mut v___y_4889_: *mut leanh::LeanObject,
    mut v___y_4890_: *mut leanh::LeanObject,
    mut v___y_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4894_: usize = 0;
    let mut v_i_boxed_4895_: usize = 0;
    let mut v_res_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4894_ = leanh::lean_unbox_usize(v_sz_4884_);
    leanh::lean_dec(v_sz_4884_);
    v_i_boxed_4895_ = leanh::lean_unbox_usize(v_i_4885_);
    leanh::lean_dec(v_i_4885_);
    v_res_4896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v___x_4882_, v_as_4883_, v_sz_boxed_4894_, v_i_boxed_4895_, v_b_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
    leanh::lean_dec(v___y_4892_);
    leanh::lean_dec_ref(v___y_4891_);
    leanh::lean_dec(v___y_4890_);
    leanh::lean_dec_ref(v___y_4889_);
    leanh::lean_dec(v___y_4888_);
    leanh::lean_dec_ref(v___y_4887_);
    leanh::lean_dec_ref(v_as_4883_);
    return v_res_4896_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(
    mut v_msgData_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
    mut v___y_4899_: *mut leanh::LeanObject,
    mut v___y_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4903_ = lean_st_ref_get(v___y_4901_);
    v_env_4904_ = leanh::lean_ctor_get(v___x_4903_, 0);
    leanh::lean_inc_ref(v_env_4904_);
    leanh::lean_dec(v___x_4903_);
    v___x_4905_ = lean_st_ref_get(v___y_4899_);
    v_mctx_4906_ = leanh::lean_ctor_get(v___x_4905_, 0);
    leanh::lean_inc_ref(v_mctx_4906_);
    leanh::lean_dec(v___x_4905_);
    v_lctx_4907_ = leanh::lean_ctor_get(v___y_4898_, 2);
    v_options_4908_ = leanh::lean_ctor_get(v___y_4900_, 2);
    leanh::lean_inc_ref(v_options_4908_);
    leanh::lean_inc_ref(v_lctx_4907_);
    v___x_4909_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4909_, 0, v_env_4904_);
    leanh::lean_ctor_set(v___x_4909_, 1, v_mctx_4906_);
    leanh::lean_ctor_set(v___x_4909_, 2, v_lctx_4907_);
    leanh::lean_ctor_set(v___x_4909_, 3, v_options_4908_);
    v___x_4910_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4910_, 0, v___x_4909_);
    leanh::lean_ctor_set(v___x_4910_, 1, v_msgData_4897_);
    v___x_4911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4911_, 0, v___x_4910_);
    return v___x_4911_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2___boxed(
    mut v_msgData_4912_: *mut leanh::LeanObject,
    mut v___y_4913_: *mut leanh::LeanObject,
    mut v___y_4914_: *mut leanh::LeanObject,
    mut v___y_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msgData_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
    leanh::lean_dec(v___y_4916_);
    leanh::lean_dec_ref(v___y_4915_);
    leanh::lean_dec(v___y_4914_);
    leanh::lean_dec_ref(v___y_4913_);
    return v_res_4918_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4919_ = leanh::lean_box(1);
    v___x_4920_ = l_Lean_MessageData_ofFormat(v___x_4919_);
    return v___x_4920_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4924_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__2;
    v___x_4925_ = l_Lean_MessageData_ofFormat(v___x_4924_);
    return v___x_4925_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(
    mut v_x_4926_: *mut leanh::LeanObject,
    mut v_x_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v_before_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_unused_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4927_) == 0 {
                    return v_x_4926_;
                } else {
                    v_head_4928_ = leanh::lean_ctor_get(v_x_4927_, 0);
                    v_tail_4929_ = leanh::lean_ctor_get(v_x_4927_, 1);
                    v_isSharedCheck_4951_ = (!leanh::lean_is_exclusive(v_x_4927_)) as u8;
                    if v_isSharedCheck_4951_ == 0 {
                        v___x_4931_ = v_x_4927_;
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4929_);
                        leanh::lean_inc(v_head_4928_);
                        leanh::lean_dec(v_x_4927_);
                        v___x_4931_ = leanh::lean_box(0);
                        v_isShared_4932_ = v_isSharedCheck_4951_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4933_ = leanh::lean_ctor_get(v_head_4928_, 0);
                v_isSharedCheck_4949_ = (!leanh::lean_is_exclusive(v_head_4928_)) as u8;
                if v_isSharedCheck_4949_ == 0 {
                    v_unused_4950_ = leanh::lean_ctor_get(v_head_4928_, 1);
                    leanh::lean_dec(v_unused_4950_);
                    v___x_4935_ = v_head_4928_;
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_4933_);
                    leanh::lean_dec(v_head_4928_);
                    v___x_4935_ = leanh::lean_box(0);
                    v_isShared_4936_ = v_isSharedCheck_4949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4937_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4936_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4935_, 7);
                    leanh::lean_ctor_set(v___x_4935_, 1, v___x_4937_);
                    leanh::lean_ctor_set(v___x_4935_, 0, v_x_4926_);
                    v___x_4939_ = v___x_4935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_x_4926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 1, v___x_4937_);
                    v___x_4939_ = v_reuseFailAlloc_4948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4940_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__3);
                if v_isShared_4932_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4931_, 7);
                    leanh::lean_ctor_set(v___x_4931_, 1, v___x_4940_);
                    leanh::lean_ctor_set(v___x_4931_, 0, v___x_4939_);
                    v___x_4942_ = v___x_4931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4947_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 1, v___x_4940_);
                    v___x_4942_ = v_reuseFailAlloc_4947_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4943_ = l_Lean_MessageData_ofSyntax(v_before_4933_);
                v___x_4944_ = l_Lean_indentD(v___x_4943_);
                v___x_4945_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4945_, 0, v___x_4942_);
                leanh::lean_ctor_set(v___x_4945_, 1, v___x_4944_);
                v_x_4926_ = v___x_4945_;
                v_x_4927_ = v_tail_4929_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(
    mut v_opts_4952_: *mut leanh::LeanObject,
    mut v_opt_4953_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4954_ = leanh::lean_ctor_get(v_opt_4953_, 0);
    v_defValue_4955_ = leanh::lean_ctor_get(v_opt_4953_, 1);
    v_map_4956_ = leanh::lean_ctor_get(v_opts_4952_, 0);
    v___x_4957_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4956_,
            v_name_4954_,
        );
    if leanh::lean_obj_tag(v___x_4957_) == 0 {
        let mut v___x_4958_: u8 = 0;
        v___x_4958_ = (leanh::lean_unbox(v_defValue_4955_) as u8);
        return v___x_4958_;
    } else {
        let mut v_val_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4959_ = leanh::lean_ctor_get(v___x_4957_, 0);
        leanh::lean_inc(v_val_4959_);
        leanh::lean_dec_ref_known(v___x_4957_, 1);
        if leanh::lean_obj_tag(v_val_4959_) == 1 {
            let mut v_v_4960_: u8 = 0;
            v_v_4960_ = leanh::lean_ctor_get_uint8(v_val_4959_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4959_, 0);
            return v_v_4960_;
        } else {
            let mut v___x_4961_: u8 = 0;
            leanh::lean_dec(v_val_4959_);
            v___x_4961_ = (leanh::lean_unbox(v_defValue_4955_) as u8);
            return v___x_4961_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5___boxed(
    mut v_opts_4962_: *mut leanh::LeanObject,
    mut v_opt_4963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4964_: u8 = 0;
    let mut v_r_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4964_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_opts_4962_, v_opt_4963_);
    leanh::lean_dec_ref(v_opt_4963_);
    leanh::lean_dec_ref(v_opts_4962_);
    v_r_4965_ = leanh::lean_box((v_res_4964_) as usize);
    return v_r_4965_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4969_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__1;
    v___x_4970_ = l_Lean_MessageData_ofFormat(v___x_4969_);
    return v___x_4970_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(
    mut v_msgData_4971_: *mut leanh::LeanObject,
    mut v_macroStack_4972_: *mut leanh::LeanObject,
    mut v___y_4973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: u8 = 0;
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4984_: u8 = 0;
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut v_unused_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4975_ = leanh::lean_ctor_get(v___y_4973_, 2);
                v___x_4976_ = l_Lean_Elab_pp_macroStack;
                v___x_4977_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__5(v_options_4975_, v___x_4976_);
                if v___x_4977_ == 0 {
                    leanh::lean_dec(v_macroStack_4972_);
                    v___x_4978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4978_, 0, v_msgData_4971_);
                    return v___x_4978_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_4972_) == 0 {
                        v___x_4979_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4979_, 0, v_msgData_4971_);
                        return v___x_4979_;
                    } else {
                        v_head_4980_ = leanh::lean_ctor_get(v_macroStack_4972_, 0);
                        leanh::lean_inc(v_head_4980_);
                        v_after_4981_ = leanh::lean_ctor_get(v_head_4980_, 1);
                        v_isSharedCheck_4996_ =
                            (!leanh::lean_is_exclusive(v_head_4980_)) as u8;
                        if v_isSharedCheck_4996_ == 0 {
                            v_unused_4997_ = leanh::lean_ctor_get(v_head_4980_, 0);
                            leanh::lean_dec(v_unused_4997_);
                            v___x_4983_ = v_head_4980_;
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_4981_);
                            leanh::lean_dec(v_head_4980_);
                            v___x_4983_ = leanh::lean_box(0);
                            v_isShared_4984_ = v_isSharedCheck_4996_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6___closed__0);
                if v_isShared_4984_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4983_, 7);
                    leanh::lean_ctor_set(v___x_4983_, 1, v___x_4985_);
                    leanh::lean_ctor_set(v___x_4983_, 0, v_msgData_4971_);
                    v___x_4987_ = v___x_4983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4995_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_msgData_4971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 1, v___x_4985_);
                    v___x_4987_ = v_reuseFailAlloc_4995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___closed__2);
                v___x_4989_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4989_, 0, v___x_4987_);
                leanh::lean_ctor_set(v___x_4989_, 1, v___x_4988_);
                v___x_4990_ = l_Lean_MessageData_ofSyntax(v_after_4981_);
                v___x_4991_ = l_Lean_indentD(v___x_4990_);
                v_msgData_4992_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_4992_, 0, v___x_4989_);
                leanh::lean_ctor_set(v_msgData_4992_, 1, v___x_4991_);
                v___x_4993_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3_spec__6(v_msgData_4992_, v_macroStack_4972_);
                v___x_4994_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4994_, 0, v___x_4993_);
                return v___x_4994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg___boxed(
    mut v_msgData_4998_: *mut leanh::LeanObject,
    mut v_macroStack_4999_: *mut leanh::LeanObject,
    mut v___y_5000_: *mut leanh::LeanObject,
    mut v___y_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5002_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_4998_, v_macroStack_4999_, v___y_5000_);
    leanh::lean_dec_ref(v___y_5000_);
    return v_res_5002_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
    mut v_msg_5003_: *mut leanh::LeanObject,
    mut v___y_5004_: *mut leanh::LeanObject,
    mut v___y_5005_: *mut leanh::LeanObject,
    mut v___y_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5020_: u8 = 0;
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5011_ = leanh::lean_ctor_get(v___y_5008_, 5);
                v___x_5012_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__2(v_msg_5003_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
                v_a_5013_ = leanh::lean_ctor_get(v___x_5012_, 0);
                leanh::lean_inc(v_a_5013_);
                leanh::lean_dec_ref(v___x_5012_);
                v_macroStack_5014_ = leanh::lean_ctor_get(v___y_5004_, 1);
                v___x_5015_ = l_Lean_Elab_getBetterRef(v_ref_5011_, v_macroStack_5014_);
                leanh::lean_inc(v_macroStack_5014_);
                v___x_5016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_a_5013_, v_macroStack_5014_, v___y_5008_);
                v_a_5017_ = leanh::lean_ctor_get(v___x_5016_, 0);
                v_isSharedCheck_5025_ = (!leanh::lean_is_exclusive(v___x_5016_)) as u8;
                if v_isSharedCheck_5025_ == 0 {
                    v___x_5019_ = v___x_5016_;
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5017_);
                    leanh::lean_dec(v___x_5016_);
                    v___x_5019_ = leanh::lean_box(0);
                    v_isShared_5020_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5021_, 0, v___x_5015_);
                leanh::lean_ctor_set(v___x_5021_, 1, v_a_5017_);
                if v_isShared_5020_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5019_, 1);
                    leanh::lean_ctor_set(v___x_5019_, 0, v___x_5021_);
                    v___x_5023_ = v___x_5019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v___x_5021_);
                    v___x_5023_ = v_reuseFailAlloc_5024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg___boxed(
    mut v_msg_5026_: *mut leanh::LeanObject,
    mut v___y_5027_: *mut leanh::LeanObject,
    mut v___y_5028_: *mut leanh::LeanObject,
    mut v___y_5029_: *mut leanh::LeanObject,
    mut v___y_5030_: *mut leanh::LeanObject,
    mut v___y_5031_: *mut leanh::LeanObject,
    mut v___y_5032_: *mut leanh::LeanObject,
    mut v___y_5033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5034_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
        v_msg_5026_,
        v___y_5027_,
        v___y_5028_,
        v___y_5029_,
        v___y_5030_,
        v___y_5031_,
        v___y_5032_,
    );
    leanh::lean_dec(v___y_5032_);
    leanh::lean_dec_ref(v___y_5031_);
    leanh::lean_dec(v___y_5030_);
    leanh::lean_dec_ref(v___y_5029_);
    leanh::lean_dec(v___y_5028_);
    leanh::lean_dec_ref(v___y_5027_);
    return v_res_5034_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5040_ = leanh::lean_box(0);
    v___x_5041_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__2;
    v___x_5042_ = l_Lean_mkConst(v___x_5041_, v___x_5040_);
    return v___x_5042_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5() -> *mut leanh::LeanObject
{
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5044_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__4;
    v___x_5045_ = l_Lean_stringToMessageData(v___x_5044_);
    return v___x_5045_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5047_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__6;
    v___x_5048_ = l_Lean_stringToMessageData(v___x_5047_);
    return v___x_5048_;
}
pub unsafe fn _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5052_ = l_Lean_Elab_Do_elabDoFor___lam__3___closed__9;
    v___x_5053_ = l_Lean_MessageData_ofFormat(v___x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__3(
    mut v___y_5054_: *mut leanh::LeanObject,
    mut v_monadInfo_5055_: *mut leanh::LeanObject,
    mut v_returnsEarly_5056_: u8,
    mut v___x_5057_: *mut leanh::LeanObject,
    mut v_a_5058_: *mut leanh::LeanObject,
    mut v___x_5059_: u8,
    mut v_e_5060_: *mut leanh::LeanObject,
    mut v___y_5061_: *mut leanh::LeanObject,
    mut v___y_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defs_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5076_: usize = 0;
    let mut v___x_5077_: usize = 0;
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_unused_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnVar_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5109_: u8 = 0;
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut v_val_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v___y_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5092_ = lean_mk_empty_array_with_capacity(v___x_5057_);
                if leanh::lean_obj_tag(v_e_5060_) == 0 {
                    if v___x_5059_ == 0 {
                        state = 13;
                        continue;
                    } else {
                        state = 5;
                        continue;
                    }
                } else {
                    state = 13;
                    continue;
                }
            }
            1 => {
                v_sz_5076_ = lean_array_size(v___y_5054_);
                v___x_5077_ = 0usize;
                v___x_5078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_elabDoFor_spec__1(v_monadInfo_5055_, v___y_5054_, v_sz_5076_, v___x_5077_, v_defs_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
                if leanh::lean_obj_tag(v___x_5078_) == 0 {
                    if v_returnsEarly_5056_ == 0 {
                        return v___x_5078_;
                    } else {
                        v_a_5079_ = leanh::lean_ctor_get(v___x_5078_, 0);
                        leanh::lean_inc(v_a_5079_);
                        v___x_5080_ = lean_array_get_size(v___y_5054_);
                        v___x_5081_ = lean_nat_dec_eq(v___x_5080_, v___x_5057_);
                        if v___x_5081_ == 0 {
                            leanh::lean_dec(v_a_5079_);
                            return v___x_5078_;
                        } else {
                            v_isSharedCheck_5090_ =
                                (!leanh::lean_is_exclusive(v___x_5078_)) as u8;
                            if v_isSharedCheck_5090_ == 0 {
                                v_unused_5091_ = leanh::lean_ctor_get(v___x_5078_, 0);
                                leanh::lean_dec(v_unused_5091_);
                                v___x_5083_ = v___x_5078_;
                                v_isShared_5084_ = v_isSharedCheck_5090_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5078_);
                                v___x_5083_ = leanh::lean_box(0);
                                v_isShared_5084_ = v_isSharedCheck_5090_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    return v___x_5078_;
                }
            }
            2 => {
                v___x_5085_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__3_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__3,
                );
                v___x_5086_ = lean_array_push(v_a_5079_, v___x_5085_);
                if v_isShared_5084_ == 0 {
                    leanh::lean_ctor_set(v___x_5083_, 0, v___x_5086_);
                    v___x_5088_ = v___x_5083_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5089_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
                    v___x_5088_ = v_reuseFailAlloc_5089_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5088_;
            }
            4 => {
                v___x_5101_ = lean_array_push(v___x_5092_, v_returnVar_5094_);
                v_defs_5069_ = v___x_5101_;
                v___y_5070_ = v___y_5095_;
                v___y_5071_ = v___y_5096_;
                v___y_5072_ = v___y_5097_;
                v___y_5073_ = v___y_5098_;
                v___y_5074_ = v___y_5099_;
                v___y_5075_ = v___y_5100_;
                state = 1;
                continue;
            }
            5 => {
                if v_returnsEarly_5056_ == 0 {
                    leanh::lean_dec(v_e_5060_);
                    leanh::lean_dec_ref(v_a_5058_);
                    v_defs_5069_ = v___x_5092_;
                    v___y_5070_ = v___y_5061_;
                    v___y_5071_ = v___y_5062_;
                    v___y_5072_ = v___y_5063_;
                    v___y_5073_ = v___y_5064_;
                    v___y_5074_ = v___y_5065_;
                    v___y_5075_ = v___y_5066_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v_e_5060_) == 0 {
                        v_resultType_5103_ = leanh::lean_ctor_get(v_a_5058_, 0);
                        leanh::lean_inc_ref(v_resultType_5103_);
                        leanh::lean_dec_ref(v_a_5058_);
                        v___x_5104_ = l_Lean_Meta_mkNone(
                            v_resultType_5103_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if leanh::lean_obj_tag(v___x_5104_) == 0 {
                            v_a_5105_ = leanh::lean_ctor_get(v___x_5104_, 0);
                            leanh::lean_inc(v_a_5105_);
                            leanh::lean_dec_ref_known(v___x_5104_, 1);
                            v_returnVar_5094_ = v_a_5105_;
                            v___y_5095_ = v___y_5061_;
                            v___y_5096_ = v___y_5062_;
                            v___y_5097_ = v___y_5063_;
                            v___y_5098_ = v___y_5064_;
                            v___y_5099_ = v___y_5065_;
                            v___y_5100_ = v___y_5066_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_5092_);
                            leanh::lean_dec_ref(v_monadInfo_5055_);
                            v_a_5106_ = leanh::lean_ctor_get(v___x_5104_, 0);
                            v_isSharedCheck_5113_ =
                                (!leanh::lean_is_exclusive(v___x_5104_)) as u8;
                            if v_isSharedCheck_5113_ == 0 {
                                v___x_5108_ = v___x_5104_;
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5106_);
                                leanh::lean_dec(v___x_5104_);
                                v___x_5108_ = leanh::lean_box(0);
                                v_isShared_5109_ = v_isSharedCheck_5113_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v_val_5114_ = leanh::lean_ctor_get(v_e_5060_, 0);
                        leanh::lean_inc(v_val_5114_);
                        leanh::lean_dec_ref_known(v_e_5060_, 1);
                        v_resultType_5115_ = leanh::lean_ctor_get(v_a_5058_, 0);
                        leanh::lean_inc_ref(v_resultType_5115_);
                        leanh::lean_dec_ref(v_a_5058_);
                        v___x_5116_ = l_Lean_Meta_mkSome(
                            v_resultType_5115_,
                            v_val_5114_,
                            v___y_5063_,
                            v___y_5064_,
                            v___y_5065_,
                            v___y_5066_,
                        );
                        if leanh::lean_obj_tag(v___x_5116_) == 0 {
                            v_a_5117_ = leanh::lean_ctor_get(v___x_5116_, 0);
                            leanh::lean_inc(v_a_5117_);
                            leanh::lean_dec_ref_known(v___x_5116_, 1);
                            v_returnVar_5094_ = v_a_5117_;
                            v___y_5095_ = v___y_5061_;
                            v___y_5096_ = v___y_5062_;
                            v___y_5097_ = v___y_5063_;
                            v___y_5098_ = v___y_5064_;
                            v___y_5099_ = v___y_5065_;
                            v___y_5100_ = v___y_5066_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_5092_);
                            leanh::lean_dec_ref(v_monadInfo_5055_);
                            v_a_5118_ = leanh::lean_ctor_get(v___x_5116_, 0);
                            v_isSharedCheck_5125_ =
                                (!leanh::lean_is_exclusive(v___x_5116_)) as u8;
                            if v_isSharedCheck_5125_ == 0 {
                                v___x_5120_ = v___x_5116_;
                                v_isShared_5121_ = v_isSharedCheck_5125_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5118_);
                                leanh::lean_dec(v___x_5116_);
                                v___x_5120_ = leanh::lean_box(0);
                                v_isShared_5121_ = v_isSharedCheck_5125_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_5109_ == 0 {
                    v___x_5111_ = v___x_5108_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
                    v___x_5111_ = v_reuseFailAlloc_5112_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5111_;
            }
            8 => {
                if v_isShared_5121_ == 0 {
                    v___x_5123_ = v___x_5120_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5123_;
            }
            10 => {
                leanh::lean_inc_ref(v___y_5127_);
                v___x_5129_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5129_, 0, v___y_5127_);
                leanh::lean_ctor_set(v___x_5129_, 1, v___y_5128_);
                v___x_5130_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__5_once),
                    _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__5,
                );
                v___x_5131_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                leanh::lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                v___x_5132_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
                    v___x_5131_,
                    v___y_5061_,
                    v___y_5062_,
                    v___y_5063_,
                    v___y_5064_,
                    v___y_5065_,
                    v___y_5066_,
                );
                v_a_5133_ = leanh::lean_ctor_get(v___x_5132_, 0);
                v_isSharedCheck_5140_ = (!leanh::lean_is_exclusive(v___x_5132_)) as u8;
                if v_isSharedCheck_5140_ == 0 {
                    v___x_5135_ = v___x_5132_;
                    v_isShared_5136_ = v_isSharedCheck_5140_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5133_);
                    leanh::lean_dec(v___x_5132_);
                    v___x_5135_ = leanh::lean_box(0);
                    v_isShared_5136_ = v_isSharedCheck_5140_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5136_ == 0 {
                    v___x_5138_ = v___x_5135_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
                    v___x_5138_ = v_reuseFailAlloc_5139_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5138_;
            }
            13 => {
                if v_returnsEarly_5056_ == 0 {
                    leanh::lean_dec_ref(v___x_5092_);
                    leanh::lean_dec_ref(v_a_5058_);
                    leanh::lean_dec_ref(v_monadInfo_5055_);
                    v___x_5142_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__7_once),
                        _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__7,
                    );
                    if leanh::lean_obj_tag(v_e_5060_) == 0 {
                        v___x_5143_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Do_elabDoFor___lam__3___closed__10),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Do_elabDoFor___lam__3___closed__10_once
                            ),
                            _init_l_Lean_Elab_Do_elabDoFor___lam__3___closed__10,
                        );
                        v___y_5127_ = v___x_5142_;
                        v___y_5128_ = v___x_5143_;
                        state = 10;
                        continue;
                    } else {
                        v_val_5144_ = leanh::lean_ctor_get(v_e_5060_, 0);
                        leanh::lean_inc(v_val_5144_);
                        leanh::lean_dec_ref_known(v_e_5060_, 1);
                        v___x_5145_ = l_Lean_MessageData_ofExpr(v_val_5144_);
                        v___y_5127_ = v___x_5142_;
                        v___y_5128_ = v___x_5145_;
                        state = 10;
                        continue;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__3___boxed(
    mut v___y_5146_: *mut leanh::LeanObject,
    mut v_monadInfo_5147_: *mut leanh::LeanObject,
    mut v_returnsEarly_5148_: *mut leanh::LeanObject,
    mut v___x_5149_: *mut leanh::LeanObject,
    mut v_a_5150_: *mut leanh::LeanObject,
    mut v___x_5151_: *mut leanh::LeanObject,
    mut v_e_5152_: *mut leanh::LeanObject,
    mut v___y_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
    mut v___y_5158_: *mut leanh::LeanObject,
    mut v___y_5159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_returnsEarly_boxed_5160_: u8 = 0;
    let mut v___x_71505__boxed_5161_: u8 = 0;
    let mut v_res_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5160_ = (leanh::lean_unbox(v_returnsEarly_5148_) as u8);
    v___x_71505__boxed_5161_ = (leanh::lean_unbox(v___x_5151_) as u8);
    v_res_5162_ = l_Lean_Elab_Do_elabDoFor___lam__3(
        v___y_5146_,
        v_monadInfo_5147_,
        v_returnsEarly_boxed_5160_,
        v___x_5149_,
        v_a_5150_,
        v___x_71505__boxed_5161_,
        v_e_5152_,
        v___y_5153_,
        v___y_5154_,
        v___y_5155_,
        v___y_5156_,
        v___y_5157_,
        v___y_5158_,
    );
    leanh::lean_dec(v___y_5158_);
    leanh::lean_dec_ref(v___y_5157_);
    leanh::lean_dec(v___y_5156_);
    leanh::lean_dec_ref(v___y_5155_);
    leanh::lean_dec(v___y_5154_);
    leanh::lean_dec_ref(v___y_5153_);
    leanh::lean_dec(v___x_5149_);
    leanh::lean_dec_ref(v___y_5146_);
    return v_res_5162_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__4(
    mut v___f_5164_: *mut leanh::LeanObject,
    mut v_u_5165_: *mut leanh::LeanObject,
    mut v___x_5166_: *mut leanh::LeanObject,
    mut v___x_5167_: *mut leanh::LeanObject,
    mut v_snd_5168_: *mut leanh::LeanObject,
    mut v___x_5169_: *mut leanh::LeanObject,
    mut v_e_5170_: *mut leanh::LeanObject,
    mut v___y_5171_: *mut leanh::LeanObject,
    mut v___y_5172_: *mut leanh::LeanObject,
    mut v___y_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
    mut v___y_5176_: *mut leanh::LeanObject,
    mut v___y_5177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5193_: u8 = 0;
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5197_: u8 = 0;
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5179_, 0, v_e_5170_);
                leanh::lean_inc(v___y_5177_);
                leanh::lean_inc_ref(v___y_5176_);
                leanh::lean_inc(v___y_5175_);
                leanh::lean_inc_ref(v___y_5174_);
                leanh::lean_inc(v___y_5173_);
                leanh::lean_inc_ref(v___y_5172_);
                v___x_5180_ = leanh::lean_apply_8(
                    v___f_5164_,
                    v___x_5179_,
                    v___y_5172_,
                    v___y_5173_,
                    v___y_5174_,
                    v___y_5175_,
                    v___y_5176_,
                    v___y_5177_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5180_) == 0 {
                    v_a_5181_ = leanh::lean_ctor_get(v___x_5180_, 0);
                    leanh::lean_inc(v_a_5181_);
                    leanh::lean_dec_ref_known(v___x_5180_, 1);
                    v___x_5182_ = l_Lean_Meta_mkProdMkN(
                        v_a_5181_,
                        v_u_5165_,
                        v___y_5174_,
                        v___y_5175_,
                        v___y_5176_,
                        v___y_5177_,
                    );
                    if leanh::lean_obj_tag(v___x_5182_) == 0 {
                        v_a_5183_ = leanh::lean_ctor_get(v___x_5182_, 0);
                        leanh::lean_inc(v_a_5183_);
                        leanh::lean_dec_ref_known(v___x_5182_, 1);
                        v_fst_5184_ = leanh::lean_ctor_get(v_a_5183_, 0);
                        leanh::lean_inc(v_fst_5184_);
                        leanh::lean_dec(v_a_5183_);
                        v___x_5185_ = l_Lean_Elab_Do_elabDoFor___lam__4___closed__0;
                        v___x_5186_ = l_Lean_Name_mkStr2(v___x_5166_, v___x_5185_);
                        v___x_5187_ = l_Lean_mkConst(v___x_5186_, v___x_5167_);
                        v___x_5188_ = l_Lean_mkAppB(v___x_5187_, v_snd_5168_, v_fst_5184_);
                        v___x_5189_ = l_Lean_Elab_Do_mkPureApp(
                            v___x_5169_,
                            v___x_5188_,
                            v___y_5171_,
                            v___y_5172_,
                            v___y_5173_,
                            v___y_5174_,
                            v___y_5175_,
                            v___y_5176_,
                            v___y_5177_,
                        );
                        return v___x_5189_;
                    } else {
                        leanh::lean_dec_ref(v___x_5169_);
                        leanh::lean_dec_ref(v_snd_5168_);
                        leanh::lean_dec(v___x_5167_);
                        leanh::lean_dec_ref(v___x_5166_);
                        v_a_5190_ = leanh::lean_ctor_get(v___x_5182_, 0);
                        v_isSharedCheck_5197_ =
                            (!leanh::lean_is_exclusive(v___x_5182_)) as u8;
                        if v_isSharedCheck_5197_ == 0 {
                            v___x_5192_ = v___x_5182_;
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5190_);
                            leanh::lean_dec(v___x_5182_);
                            v___x_5192_ = leanh::lean_box(0);
                            v_isShared_5193_ = v_isSharedCheck_5197_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5169_);
                    leanh::lean_dec_ref(v_snd_5168_);
                    leanh::lean_dec(v___x_5167_);
                    leanh::lean_dec_ref(v___x_5166_);
                    leanh::lean_dec(v_u_5165_);
                    v_a_5198_ = leanh::lean_ctor_get(v___x_5180_, 0);
                    v_isSharedCheck_5205_ = (!leanh::lean_is_exclusive(v___x_5180_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5200_ = v___x_5180_;
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5198_);
                        leanh::lean_dec(v___x_5180_);
                        v___x_5200_ = leanh::lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5193_ == 0 {
                    v___x_5195_ = v___x_5192_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5196_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5196_, 0, v_a_5190_);
                    v___x_5195_ = v_reuseFailAlloc_5196_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5195_;
            }
            3 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5203_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__4___boxed(
    mut v___f_5206_: *mut leanh::LeanObject,
    mut v_u_5207_: *mut leanh::LeanObject,
    mut v___x_5208_: *mut leanh::LeanObject,
    mut v___x_5209_: *mut leanh::LeanObject,
    mut v_snd_5210_: *mut leanh::LeanObject,
    mut v___x_5211_: *mut leanh::LeanObject,
    mut v_e_5212_: *mut leanh::LeanObject,
    mut v___y_5213_: *mut leanh::LeanObject,
    mut v___y_5214_: *mut leanh::LeanObject,
    mut v___y_5215_: *mut leanh::LeanObject,
    mut v___y_5216_: *mut leanh::LeanObject,
    mut v___y_5217_: *mut leanh::LeanObject,
    mut v___y_5218_: *mut leanh::LeanObject,
    mut v___y_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5221_ = l_Lean_Elab_Do_elabDoFor___lam__4(
        v___f_5206_,
        v_u_5207_,
        v___x_5208_,
        v___x_5209_,
        v_snd_5210_,
        v___x_5211_,
        v_e_5212_,
        v___y_5213_,
        v___y_5214_,
        v___y_5215_,
        v___y_5216_,
        v___y_5217_,
        v___y_5218_,
        v___y_5219_,
    );
    leanh::lean_dec(v___y_5219_);
    leanh::lean_dec_ref(v___y_5218_);
    leanh::lean_dec(v___y_5217_);
    leanh::lean_dec_ref(v___y_5216_);
    leanh::lean_dec(v___y_5215_);
    leanh::lean_dec_ref(v___y_5214_);
    leanh::lean_dec_ref(v___y_5213_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__5(
    mut v___f_5223_: *mut leanh::LeanObject,
    mut v___x_5224_: *mut leanh::LeanObject,
    mut v_u_5225_: *mut leanh::LeanObject,
    mut v___x_5226_: *mut leanh::LeanObject,
    mut v___x_5227_: *mut leanh::LeanObject,
    mut v_snd_5228_: *mut leanh::LeanObject,
    mut v___x_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v_a_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_5236_);
                leanh::lean_inc_ref(v___y_5235_);
                leanh::lean_inc(v___y_5234_);
                leanh::lean_inc_ref(v___y_5233_);
                leanh::lean_inc(v___y_5232_);
                leanh::lean_inc_ref(v___y_5231_);
                v___x_5238_ = leanh::lean_apply_8(
                    v___f_5223_,
                    v___x_5224_,
                    v___y_5231_,
                    v___y_5232_,
                    v___y_5233_,
                    v___y_5234_,
                    v___y_5235_,
                    v___y_5236_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5238_) == 0 {
                    v_a_5239_ = leanh::lean_ctor_get(v___x_5238_, 0);
                    leanh::lean_inc(v_a_5239_);
                    leanh::lean_dec_ref_known(v___x_5238_, 1);
                    v___x_5240_ = l_Lean_Meta_mkProdMkN(
                        v_a_5239_,
                        v_u_5225_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                        v___y_5236_,
                    );
                    if leanh::lean_obj_tag(v___x_5240_) == 0 {
                        v_a_5241_ = leanh::lean_ctor_get(v___x_5240_, 0);
                        leanh::lean_inc(v_a_5241_);
                        leanh::lean_dec_ref_known(v___x_5240_, 1);
                        v_fst_5242_ = leanh::lean_ctor_get(v_a_5241_, 0);
                        leanh::lean_inc(v_fst_5242_);
                        leanh::lean_dec(v_a_5241_);
                        v___x_5243_ = l_Lean_Elab_Do_elabDoFor___lam__5___closed__0;
                        v___x_5244_ = l_Lean_Name_mkStr2(v___x_5226_, v___x_5243_);
                        v___x_5245_ = l_Lean_mkConst(v___x_5244_, v___x_5227_);
                        v___x_5246_ = l_Lean_mkAppB(v___x_5245_, v_snd_5228_, v_fst_5242_);
                        v___x_5247_ = l_Lean_Elab_Do_mkPureApp(
                            v___x_5229_,
                            v___x_5246_,
                            v___y_5230_,
                            v___y_5231_,
                            v___y_5232_,
                            v___y_5233_,
                            v___y_5234_,
                            v___y_5235_,
                            v___y_5236_,
                        );
                        return v___x_5247_;
                    } else {
                        leanh::lean_dec_ref(v___x_5229_);
                        leanh::lean_dec_ref(v_snd_5228_);
                        leanh::lean_dec(v___x_5227_);
                        leanh::lean_dec_ref(v___x_5226_);
                        v_a_5248_ = leanh::lean_ctor_get(v___x_5240_, 0);
                        v_isSharedCheck_5255_ =
                            (!leanh::lean_is_exclusive(v___x_5240_)) as u8;
                        if v_isSharedCheck_5255_ == 0 {
                            v___x_5250_ = v___x_5240_;
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5248_);
                            leanh::lean_dec(v___x_5240_);
                            v___x_5250_ = leanh::lean_box(0);
                            v_isShared_5251_ = v_isSharedCheck_5255_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5229_);
                    leanh::lean_dec_ref(v_snd_5228_);
                    leanh::lean_dec(v___x_5227_);
                    leanh::lean_dec_ref(v___x_5226_);
                    leanh::lean_dec(v_u_5225_);
                    v_a_5256_ = leanh::lean_ctor_get(v___x_5238_, 0);
                    v_isSharedCheck_5263_ = (!leanh::lean_is_exclusive(v___x_5238_)) as u8;
                    if v_isSharedCheck_5263_ == 0 {
                        v___x_5258_ = v___x_5238_;
                        v_isShared_5259_ = v_isSharedCheck_5263_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5256_);
                        leanh::lean_dec(v___x_5238_);
                        v___x_5258_ = leanh::lean_box(0);
                        v_isShared_5259_ = v_isSharedCheck_5263_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5251_ == 0 {
                    v___x_5253_ = v___x_5250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5254_, 0, v_a_5248_);
                    v___x_5253_ = v_reuseFailAlloc_5254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5253_;
            }
            3 => {
                if v_isShared_5259_ == 0 {
                    v___x_5261_ = v___x_5258_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5262_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5262_, 0, v_a_5256_);
                    v___x_5261_ = v_reuseFailAlloc_5262_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__5___boxed(
    mut v___f_5264_: *mut leanh::LeanObject,
    mut v___x_5265_: *mut leanh::LeanObject,
    mut v_u_5266_: *mut leanh::LeanObject,
    mut v___x_5267_: *mut leanh::LeanObject,
    mut v___x_5268_: *mut leanh::LeanObject,
    mut v_snd_5269_: *mut leanh::LeanObject,
    mut v___x_5270_: *mut leanh::LeanObject,
    mut v___y_5271_: *mut leanh::LeanObject,
    mut v___y_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
    mut v___y_5274_: *mut leanh::LeanObject,
    mut v___y_5275_: *mut leanh::LeanObject,
    mut v___y_5276_: *mut leanh::LeanObject,
    mut v___y_5277_: *mut leanh::LeanObject,
    mut v___y_5278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5279_ = l_Lean_Elab_Do_elabDoFor___lam__5(
        v___f_5264_,
        v___x_5265_,
        v_u_5266_,
        v___x_5267_,
        v___x_5268_,
        v_snd_5269_,
        v___x_5270_,
        v___y_5271_,
        v___y_5272_,
        v___y_5273_,
        v___y_5274_,
        v___y_5275_,
        v___y_5276_,
        v___y_5277_,
    );
    leanh::lean_dec(v___y_5277_);
    leanh::lean_dec_ref(v___y_5276_);
    leanh::lean_dec(v___y_5275_);
    leanh::lean_dec_ref(v___y_5274_);
    leanh::lean_dec(v___y_5273_);
    leanh::lean_dec_ref(v___y_5272_);
    leanh::lean_dec_ref(v___y_5271_);
    return v_res_5279_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__6(
    mut v___f_5280_: *mut leanh::LeanObject,
    mut v___x_5281_: *mut leanh::LeanObject,
    mut v_u_5282_: *mut leanh::LeanObject,
    mut v___x_5283_: *mut leanh::LeanObject,
    mut v___x_5284_: *mut leanh::LeanObject,
    mut v_snd_5285_: *mut leanh::LeanObject,
    mut v___x_5286_: *mut leanh::LeanObject,
    mut v___y_5287_: *mut leanh::LeanObject,
    mut v___y_5288_: *mut leanh::LeanObject,
    mut v___y_5289_: *mut leanh::LeanObject,
    mut v___y_5290_: *mut leanh::LeanObject,
    mut v___y_5291_: *mut leanh::LeanObject,
    mut v___y_5292_: *mut leanh::LeanObject,
    mut v___y_5293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v_a_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5316_: u8 = 0;
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_5293_);
                leanh::lean_inc_ref(v___y_5292_);
                leanh::lean_inc(v___y_5291_);
                leanh::lean_inc_ref(v___y_5290_);
                leanh::lean_inc(v___y_5289_);
                leanh::lean_inc_ref(v___y_5288_);
                v___x_5295_ = leanh::lean_apply_8(
                    v___f_5280_,
                    v___x_5281_,
                    v___y_5288_,
                    v___y_5289_,
                    v___y_5290_,
                    v___y_5291_,
                    v___y_5292_,
                    v___y_5293_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5295_) == 0 {
                    v_a_5296_ = leanh::lean_ctor_get(v___x_5295_, 0);
                    leanh::lean_inc(v_a_5296_);
                    leanh::lean_dec_ref_known(v___x_5295_, 1);
                    v___x_5297_ = l_Lean_Meta_mkProdMkN(
                        v_a_5296_,
                        v_u_5282_,
                        v___y_5290_,
                        v___y_5291_,
                        v___y_5292_,
                        v___y_5293_,
                    );
                    if leanh::lean_obj_tag(v___x_5297_) == 0 {
                        v_a_5298_ = leanh::lean_ctor_get(v___x_5297_, 0);
                        leanh::lean_inc(v_a_5298_);
                        leanh::lean_dec_ref_known(v___x_5297_, 1);
                        v_fst_5299_ = leanh::lean_ctor_get(v_a_5298_, 0);
                        leanh::lean_inc(v_fst_5299_);
                        leanh::lean_dec(v_a_5298_);
                        v___x_5300_ = l_Lean_Elab_Do_elabDoFor___lam__4___closed__0;
                        v___x_5301_ = l_Lean_Name_mkStr2(v___x_5283_, v___x_5300_);
                        v___x_5302_ = l_Lean_mkConst(v___x_5301_, v___x_5284_);
                        v___x_5303_ = l_Lean_mkAppB(v___x_5302_, v_snd_5285_, v_fst_5299_);
                        v___x_5304_ = l_Lean_Elab_Do_mkPureApp(
                            v___x_5286_,
                            v___x_5303_,
                            v___y_5287_,
                            v___y_5288_,
                            v___y_5289_,
                            v___y_5290_,
                            v___y_5291_,
                            v___y_5292_,
                            v___y_5293_,
                        );
                        return v___x_5304_;
                    } else {
                        leanh::lean_dec_ref(v___x_5286_);
                        leanh::lean_dec_ref(v_snd_5285_);
                        leanh::lean_dec(v___x_5284_);
                        leanh::lean_dec_ref(v___x_5283_);
                        v_a_5305_ = leanh::lean_ctor_get(v___x_5297_, 0);
                        v_isSharedCheck_5312_ =
                            (!leanh::lean_is_exclusive(v___x_5297_)) as u8;
                        if v_isSharedCheck_5312_ == 0 {
                            v___x_5307_ = v___x_5297_;
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5305_);
                            leanh::lean_dec(v___x_5297_);
                            v___x_5307_ = leanh::lean_box(0);
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5286_);
                    leanh::lean_dec_ref(v_snd_5285_);
                    leanh::lean_dec(v___x_5284_);
                    leanh::lean_dec_ref(v___x_5283_);
                    leanh::lean_dec(v_u_5282_);
                    v_a_5313_ = leanh::lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5320_ = (!leanh::lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5320_ == 0 {
                        v___x_5315_ = v___x_5295_;
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5313_);
                        leanh::lean_dec(v___x_5295_);
                        v___x_5315_ = leanh::lean_box(0);
                        v_isShared_5316_ = v_isSharedCheck_5320_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5308_ == 0 {
                    v___x_5310_ = v___x_5307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5311_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
                    v___x_5310_ = v_reuseFailAlloc_5311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5310_;
            }
            3 => {
                if v_isShared_5316_ == 0 {
                    v___x_5318_ = v___x_5315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
                    v___x_5318_ = v_reuseFailAlloc_5319_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__6___boxed(
    mut v___f_5321_: *mut leanh::LeanObject,
    mut v___x_5322_: *mut leanh::LeanObject,
    mut v_u_5323_: *mut leanh::LeanObject,
    mut v___x_5324_: *mut leanh::LeanObject,
    mut v___x_5325_: *mut leanh::LeanObject,
    mut v_snd_5326_: *mut leanh::LeanObject,
    mut v___x_5327_: *mut leanh::LeanObject,
    mut v___y_5328_: *mut leanh::LeanObject,
    mut v___y_5329_: *mut leanh::LeanObject,
    mut v___y_5330_: *mut leanh::LeanObject,
    mut v___y_5331_: *mut leanh::LeanObject,
    mut v___y_5332_: *mut leanh::LeanObject,
    mut v___y_5333_: *mut leanh::LeanObject,
    mut v___y_5334_: *mut leanh::LeanObject,
    mut v___y_5335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5336_ = l_Lean_Elab_Do_elabDoFor___lam__6(
        v___f_5321_,
        v___x_5322_,
        v_u_5323_,
        v___x_5324_,
        v___x_5325_,
        v_snd_5326_,
        v___x_5327_,
        v___y_5328_,
        v___y_5329_,
        v___y_5330_,
        v___y_5331_,
        v___y_5332_,
        v___y_5333_,
        v___y_5334_,
    );
    leanh::lean_dec(v___y_5334_);
    leanh::lean_dec_ref(v___y_5333_);
    leanh::lean_dec(v___y_5332_);
    leanh::lean_dec_ref(v___y_5331_);
    leanh::lean_dec(v___y_5330_);
    leanh::lean_dec_ref(v___y_5329_);
    leanh::lean_dec_ref(v___y_5328_);
    return v_res_5336_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7(
    mut v___x_5337_: *mut leanh::LeanObject,
    mut v___f_5338_: *mut leanh::LeanObject,
    mut v___f_5339_: *mut leanh::LeanObject,
    mut v___x_5340_: *mut leanh::LeanObject,
    mut v___x_5341_: *mut leanh::LeanObject,
    mut v___y_5342_: *mut leanh::LeanObject,
    mut v___y_5343_: *mut leanh::LeanObject,
    mut v___y_5344_: *mut leanh::LeanObject,
    mut v___y_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
    mut v___y_5347_: *mut leanh::LeanObject,
    mut v___y_5348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_monadInfo_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVarDefs_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contInfo_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deadCode_5354_: u8 = 0;
    let mut v_ops_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5363_: u8 = 0;
    let mut v_unused_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_monadInfo_5350_ = leanh::lean_ctor_get(v___y_5342_, 0);
                v_mutVars_5351_ = leanh::lean_ctor_get(v___y_5342_, 1);
                v_mutVarDefs_5352_ = leanh::lean_ctor_get(v___y_5342_, 2);
                v_contInfo_5353_ = leanh::lean_ctor_get(v___y_5342_, 4);
                v_deadCode_5354_ = leanh::lean_ctor_get_uint8(
                    v___y_5342_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                v_ops_5355_ = leanh::lean_ctor_get(v___y_5342_, 5);
                v_isSharedCheck_5363_ = (!leanh::lean_is_exclusive(v___y_5342_)) as u8;
                if v_isSharedCheck_5363_ == 0 {
                    v_unused_5364_ = leanh::lean_ctor_get(v___y_5342_, 3);
                    leanh::lean_dec(v_unused_5364_);
                    v___x_5357_ = v___y_5342_;
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ops_5355_);
                    leanh::lean_inc(v_contInfo_5353_);
                    leanh::lean_inc(v_mutVarDefs_5352_);
                    leanh::lean_inc(v_mutVars_5351_);
                    leanh::lean_inc(v_monadInfo_5350_);
                    leanh::lean_dec(v___y_5342_);
                    v___x_5357_ = leanh::lean_box(0);
                    v_isShared_5358_ = v_isSharedCheck_5363_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5358_ == 0 {
                    leanh::lean_ctor_set(v___x_5357_, 3, v___x_5337_);
                    v___x_5360_ = v___x_5357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = leanh::lean_alloc_ctor(0, 6, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_monadInfo_5350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 1, v_mutVars_5351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 2, v_mutVarDefs_5352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 3, v___x_5337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 4, v_contInfo_5353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 5, v_ops_5355_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5362_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                        v_deadCode_5354_,
                    );
                    v___x_5360_ = v_reuseFailAlloc_5362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5361_ = l_Lean_Elab_Do_enterLoopBody___redArg(
                    v___f_5338_,
                    v___f_5339_,
                    v___x_5340_,
                    v___x_5341_,
                    v___x_5360_,
                    v___y_5343_,
                    v___y_5344_,
                    v___y_5345_,
                    v___y_5346_,
                    v___y_5347_,
                    v___y_5348_,
                );
                leanh::lean_dec_ref(v___x_5360_);
                return v___x_5361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__7___boxed(
    mut v___x_5365_: *mut leanh::LeanObject,
    mut v___f_5366_: *mut leanh::LeanObject,
    mut v___f_5367_: *mut leanh::LeanObject,
    mut v___x_5368_: *mut leanh::LeanObject,
    mut v___x_5369_: *mut leanh::LeanObject,
    mut v___y_5370_: *mut leanh::LeanObject,
    mut v___y_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ = l_Lean_Elab_Do_elabDoFor___lam__7(
        v___x_5365_,
        v___f_5366_,
        v___f_5367_,
        v___x_5368_,
        v___x_5369_,
        v___y_5370_,
        v___y_5371_,
        v___y_5372_,
        v___y_5373_,
        v___y_5374_,
        v___y_5375_,
        v___y_5376_,
    );
    leanh::lean_dec(v___y_5376_);
    leanh::lean_dec_ref(v___y_5375_);
    leanh::lean_dec(v___y_5374_);
    leanh::lean_dec_ref(v___y_5373_);
    leanh::lean_dec(v___y_5372_);
    leanh::lean_dec_ref(v___y_5371_);
    return v_res_5378_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8(
    mut v_a_5382_: *mut leanh::LeanObject,
    mut v_a_5383_: *mut leanh::LeanObject,
    mut v_u_5384_: *mut leanh::LeanObject,
    mut v_snd_5385_: *mut leanh::LeanObject,
    mut v___f_5386_: *mut leanh::LeanObject,
    mut v___x_5387_: *mut leanh::LeanObject,
    mut v_body_5388_: *mut leanh::LeanObject,
    mut v___x_5389_: u8,
    mut v___y_5390_: *mut leanh::LeanObject,
    mut v_xh_5391_: *mut leanh::LeanObject,
    mut v_loopS_5392_: *mut leanh::LeanObject,
    mut v___y_5393_: *mut leanh::LeanObject,
    mut v___y_5394_: *mut leanh::LeanObject,
    mut v___y_5395_: *mut leanh::LeanObject,
    mut v___y_5396_: *mut leanh::LeanObject,
    mut v___y_5397_: *mut leanh::LeanObject,
    mut v___y_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_resultType_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v_resultName_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_unused_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_unused_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_resultType_5401_ = leanh::lean_ctor_get(v_a_5382_, 0);
                v_isSharedCheck_5438_ = (!leanh::lean_is_exclusive(v_a_5382_)) as u8;
                if v_isSharedCheck_5438_ == 0 {
                    v_unused_5439_ = leanh::lean_ctor_get(v_a_5382_, 1);
                    leanh::lean_dec(v_unused_5439_);
                    v___x_5403_ = v_a_5382_;
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_resultType_5401_);
                    leanh::lean_dec(v_a_5382_);
                    v___x_5403_ = leanh::lean_box(0);
                    v_isShared_5404_ = v_isSharedCheck_5438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_resultName_5405_ = leanh::lean_ctor_get(v_a_5383_, 0);
                v_resultType_5406_ = leanh::lean_ctor_get(v_a_5383_, 1);
                v_isSharedCheck_5436_ = (!leanh::lean_is_exclusive(v_a_5383_)) as u8;
                if v_isSharedCheck_5436_ == 0 {
                    v_unused_5437_ = leanh::lean_ctor_get(v_a_5383_, 2);
                    leanh::lean_dec(v_unused_5437_);
                    v___x_5408_ = v_a_5383_;
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_resultType_5406_);
                    leanh::lean_inc(v_resultName_5405_);
                    leanh::lean_dec(v_a_5383_);
                    v___x_5408_ = leanh::lean_box(0);
                    v_isShared_5409_ = v_isSharedCheck_5436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5410_ = l_Lean_Expr_fvarId_x21(v_loopS_5392_);
                v___x_5411_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__0;
                v___x_5412_ = l_Lean_Elab_Do_elabDoFor___lam__8___closed__1;
                v___x_5413_ = leanh::lean_box(0);
                leanh::lean_inc_n(v_u_5384_, 3);
                v___x_5414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5414_, 0, v_u_5384_);
                leanh::lean_ctor_set(v___x_5414_, 1, v___x_5413_);
                leanh::lean_inc_ref_n(v___x_5414_, 3);
                v___x_5415_ = l_Lean_mkConst(v___x_5412_, v___x_5414_);
                leanh::lean_inc_ref_n(v_snd_5385_, 3);
                v___x_5416_ = l_Lean_Expr_app___override(v___x_5415_, v_snd_5385_);
                leanh::lean_inc_ref_n(v___x_5416_, 3);
                leanh::lean_inc_ref_n(v___f_5386_, 2);
                v___f_5417_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__4___boxed as *mut core::ffi::c_void,
                    15,
                    6,
                );
                leanh::lean_closure_set(v___f_5417_, 0, v___f_5386_);
                leanh::lean_closure_set(v___f_5417_, 1, v_u_5384_);
                leanh::lean_closure_set(v___f_5417_, 2, v___x_5411_);
                leanh::lean_closure_set(v___f_5417_, 3, v___x_5414_);
                leanh::lean_closure_set(v___f_5417_, 4, v_snd_5385_);
                leanh::lean_closure_set(v___f_5417_, 5, v___x_5416_);
                leanh::lean_inc(v___x_5387_);
                v___f_5418_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__5___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                leanh::lean_closure_set(v___f_5418_, 0, v___f_5386_);
                leanh::lean_closure_set(v___f_5418_, 1, v___x_5387_);
                leanh::lean_closure_set(v___f_5418_, 2, v_u_5384_);
                leanh::lean_closure_set(v___f_5418_, 3, v___x_5411_);
                leanh::lean_closure_set(v___f_5418_, 4, v___x_5414_);
                leanh::lean_closure_set(v___f_5418_, 5, v_snd_5385_);
                leanh::lean_closure_set(v___f_5418_, 6, v___x_5416_);
                v___f_5419_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__6___boxed as *mut core::ffi::c_void,
                    15,
                    7,
                );
                leanh::lean_closure_set(v___f_5419_, 0, v___f_5386_);
                leanh::lean_closure_set(v___f_5419_, 1, v___x_5387_);
                leanh::lean_closure_set(v___f_5419_, 2, v_u_5384_);
                leanh::lean_closure_set(v___f_5419_, 3, v___x_5411_);
                leanh::lean_closure_set(v___f_5419_, 4, v___x_5414_);
                leanh::lean_closure_set(v___f_5419_, 5, v_snd_5385_);
                leanh::lean_closure_set(v___f_5419_, 6, v___x_5416_);
                if v_isShared_5404_ == 0 {
                    leanh::lean_ctor_set(v___x_5403_, 1, v___f_5417_);
                    v___x_5421_ = v___x_5403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_resultType_5401_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___f_5417_);
                    v___x_5421_ = v_reuseFailAlloc_5435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5422_ = 1;
                leanh::lean_inc_ref(v___f_5418_);
                if v_isShared_5409_ == 0 {
                    leanh::lean_ctor_set(v___x_5408_, 2, v___f_5418_);
                    v___x_5424_ = v___x_5408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5434_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_resultName_5405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_resultType_5406_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 2, v___f_5418_);
                    v___x_5424_ = v_reuseFailAlloc_5434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5424_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_5422_,
                );
                v___x_5425_ = leanh::lean_box((v___x_5389_) as usize);
                v___x_5426_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoSeq___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_5426_, 0, v_body_5388_);
                leanh::lean_closure_set(v___x_5426_, 1, v___x_5424_);
                leanh::lean_closure_set(v___x_5426_, 2, v___x_5425_);
                v___f_5427_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__7___boxed as *mut core::ffi::c_void,
                    13,
                    5,
                );
                leanh::lean_closure_set(v___f_5427_, 0, v___x_5416_);
                leanh::lean_closure_set(v___f_5427_, 1, v___f_5419_);
                leanh::lean_closure_set(v___f_5427_, 2, v___f_5418_);
                leanh::lean_closure_set(v___f_5427_, 3, v___x_5421_);
                leanh::lean_closure_set(v___f_5427_, 4, v___x_5426_);
                v___x_5428_ = l_Lean_Elab_Do_bindMutVarsFromTuple(
                    v___y_5390_,
                    v___x_5410_,
                    v___f_5427_,
                    v___y_5393_,
                    v___y_5394_,
                    v___y_5395_,
                    v___y_5396_,
                    v___y_5397_,
                    v___y_5398_,
                    v___y_5399_,
                );
                if leanh::lean_obj_tag(v___x_5428_) == 0 {
                    v_a_5429_ = leanh::lean_ctor_get(v___x_5428_, 0);
                    leanh::lean_inc(v_a_5429_);
                    leanh::lean_dec_ref_known(v___x_5428_, 1);
                    v___x_5430_ = lean_array_push(v_xh_5391_, v_loopS_5392_);
                    v___x_5431_ = 0;
                    v___x_5432_ = 1;
                    v___x_5433_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_5430_,
                        v_a_5429_,
                        v___x_5431_,
                        v___x_5389_,
                        v___x_5431_,
                        v___x_5389_,
                        v___x_5432_,
                        v___y_5396_,
                        v___y_5397_,
                        v___y_5398_,
                        v___y_5399_,
                    );
                    leanh::lean_dec_ref(v___x_5430_);
                    return v___x_5433_;
                } else {
                    leanh::lean_dec_ref(v_loopS_5392_);
                    leanh::lean_dec_ref(v_xh_5391_);
                    return v___x_5428_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__8___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5440_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_5441_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_u_5442_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_snd_5443_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___f_5444_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_5445_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_body_5446_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5447_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5448_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_xh_5449_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_loopS_5450_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5451_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5452_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5453_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5454_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5455_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5456_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5457_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_5458_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___x_72062__boxed_5459_: u8 = 0;
    let mut v_res_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_72062__boxed_5459_ = (leanh::lean_unbox(v___x_5447_) as u8);
    v_res_5460_ = l_Lean_Elab_Do_elabDoFor___lam__8(
        v_a_5440_,
        v_a_5441_,
        v_u_5442_,
        v_snd_5443_,
        v___f_5444_,
        v___x_5445_,
        v_body_5446_,
        v___x_72062__boxed_5459_,
        v___y_5448_,
        v_xh_5449_,
        v_loopS_5450_,
        v___y_5451_,
        v___y_5452_,
        v___y_5453_,
        v___y_5454_,
        v___y_5455_,
        v___y_5456_,
        v___y_5457_,
    );
    leanh::lean_dec(v___y_5457_);
    leanh::lean_dec_ref(v___y_5456_);
    leanh::lean_dec(v___y_5455_);
    leanh::lean_dec_ref(v___y_5454_);
    leanh::lean_dec(v___y_5453_);
    leanh::lean_dec_ref(v___y_5452_);
    leanh::lean_dec_ref(v___y_5451_);
    return v_res_5460_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__9(
    mut v___x_5461_: *mut leanh::LeanObject,
    mut v___x_5462_: *mut leanh::LeanObject,
    mut v_x_5463_: *mut leanh::LeanObject,
    mut v_a_5464_: *mut leanh::LeanObject,
    mut v_a_5465_: *mut leanh::LeanObject,
    mut v_u_5466_: *mut leanh::LeanObject,
    mut v_snd_5467_: *mut leanh::LeanObject,
    mut v___f_5468_: *mut leanh::LeanObject,
    mut v___x_5469_: *mut leanh::LeanObject,
    mut v_body_5470_: *mut leanh::LeanObject,
    mut v___x_5471_: u8,
    mut v___y_5472_: *mut leanh::LeanObject,
    mut v_a_5473_: *mut leanh::LeanObject,
    mut v_h_x3f_5474_: *mut leanh::LeanObject,
    mut v___x_5475_: *mut leanh::LeanObject,
    mut v_xh_5476_: *mut leanh::LeanObject,
    mut v___y_5477_: *mut leanh::LeanObject,
    mut v___y_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: u8 = 0;
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5506_: u8 = 0;
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5510_: u8 = 0;
    let mut v_a_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5485_ = lean_array_get_borrowed(v___x_5461_, v_xh_5476_, v___x_5462_);
                leanh::lean_inc(v___x_5485_);
                v___x_5486_ = l_Lean_Elab_Term_addLocalVarInfo(
                    v_x_5463_,
                    v___x_5485_,
                    v___y_5478_,
                    v___y_5479_,
                    v___y_5480_,
                    v___y_5481_,
                    v___y_5482_,
                    v___y_5483_,
                );
                if leanh::lean_obj_tag(v___x_5486_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5486_, 1);
                    v___x_5487_ = leanh::lean_box((v___x_5471_) as usize);
                    leanh::lean_inc_ref(v_xh_5476_);
                    leanh::lean_inc_ref(v_snd_5467_);
                    v___f_5488_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__8___boxed as *mut core::ffi::c_void,
                        19,
                        10,
                    );
                    leanh::lean_closure_set(v___f_5488_, 0, v_a_5464_);
                    leanh::lean_closure_set(v___f_5488_, 1, v_a_5465_);
                    leanh::lean_closure_set(v___f_5488_, 2, v_u_5466_);
                    leanh::lean_closure_set(v___f_5488_, 3, v_snd_5467_);
                    leanh::lean_closure_set(v___f_5488_, 4, v___f_5468_);
                    leanh::lean_closure_set(v___f_5488_, 5, v___x_5469_);
                    leanh::lean_closure_set(v___f_5488_, 6, v_body_5470_);
                    leanh::lean_closure_set(v___f_5488_, 7, v___x_5487_);
                    leanh::lean_closure_set(v___f_5488_, 8, v___y_5472_);
                    leanh::lean_closure_set(v___f_5488_, 9, v_xh_5476_);
                    if leanh::lean_obj_tag(v_h_x3f_5474_) == 1 {
                        v_val_5500_ = leanh::lean_ctor_get(v_h_x3f_5474_, 0);
                        leanh::lean_inc(v_val_5500_);
                        leanh::lean_dec_ref_known(v_h_x3f_5474_, 1);
                        v___x_5501_ = lean_array_get(v___x_5461_, v_xh_5476_, v___x_5475_);
                        leanh::lean_dec_ref(v_xh_5476_);
                        v___x_5502_ = l_Lean_Elab_Term_addLocalVarInfo(
                            v_val_5500_,
                            v___x_5501_,
                            v___y_5478_,
                            v___y_5479_,
                            v___y_5480_,
                            v___y_5481_,
                            v___y_5482_,
                            v___y_5483_,
                        );
                        if leanh::lean_obj_tag(v___x_5502_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5502_, 1);
                            v___y_5490_ = v___y_5477_;
                            v___y_5491_ = v___y_5478_;
                            v___y_5492_ = v___y_5479_;
                            v___y_5493_ = v___y_5480_;
                            v___y_5494_ = v___y_5481_;
                            v___y_5495_ = v___y_5482_;
                            v___y_5496_ = v___y_5483_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___f_5488_);
                            leanh::lean_dec(v_a_5473_);
                            leanh::lean_dec_ref(v_snd_5467_);
                            v_a_5503_ = leanh::lean_ctor_get(v___x_5502_, 0);
                            v_isSharedCheck_5510_ =
                                (!leanh::lean_is_exclusive(v___x_5502_)) as u8;
                            if v_isSharedCheck_5510_ == 0 {
                                v___x_5505_ = v___x_5502_;
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5503_);
                                leanh::lean_dec(v___x_5502_);
                                v___x_5505_ = leanh::lean_box(0);
                                v_isShared_5506_ = v_isSharedCheck_5510_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_xh_5476_);
                        leanh::lean_dec(v_h_x3f_5474_);
                        v___y_5490_ = v___y_5477_;
                        v___y_5491_ = v___y_5478_;
                        v___y_5492_ = v___y_5479_;
                        v___y_5493_ = v___y_5480_;
                        v___y_5494_ = v___y_5481_;
                        v___y_5495_ = v___y_5482_;
                        v___y_5496_ = v___y_5483_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_xh_5476_);
                    leanh::lean_dec(v_h_x3f_5474_);
                    leanh::lean_dec(v_a_5473_);
                    leanh::lean_dec(v___y_5472_);
                    leanh::lean_dec(v_body_5470_);
                    leanh::lean_dec(v___x_5469_);
                    leanh::lean_dec_ref(v___f_5468_);
                    leanh::lean_dec_ref(v_snd_5467_);
                    leanh::lean_dec(v_u_5466_);
                    leanh::lean_dec_ref(v_a_5465_);
                    leanh::lean_dec_ref(v_a_5464_);
                    v_a_5511_ = leanh::lean_ctor_get(v___x_5486_, 0);
                    v_isSharedCheck_5518_ = (!leanh::lean_is_exclusive(v___x_5486_)) as u8;
                    if v_isSharedCheck_5518_ == 0 {
                        v___x_5513_ = v___x_5486_;
                        v_isShared_5514_ = v_isSharedCheck_5518_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5511_);
                        leanh::lean_dec(v___x_5486_);
                        v___x_5513_ = leanh::lean_box(0);
                        v_isShared_5514_ = v_isSharedCheck_5518_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5497_ = 0;
                v___x_5498_ = 1;
                v___x_5499_ =
                    l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
                        v_a_5473_,
                        v___x_5497_,
                        v_snd_5467_,
                        v___f_5488_,
                        v___x_5498_,
                        v___y_5490_,
                        v___y_5491_,
                        v___y_5492_,
                        v___y_5493_,
                        v___y_5494_,
                        v___y_5495_,
                        v___y_5496_,
                    );
                return v___x_5499_;
            }
            2 => {
                if v_isShared_5506_ == 0 {
                    v___x_5508_ = v___x_5505_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
                    v___x_5508_ = v_reuseFailAlloc_5509_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5508_;
            }
            4 => {
                if v_isShared_5514_ == 0 {
                    v___x_5516_ = v___x_5513_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
                    v___x_5516_ = v_reuseFailAlloc_5517_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__9___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5519_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5520_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_x_5521_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_a_5522_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_5523_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_u_5524_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_snd_5525_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_5526_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5527_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_body_5528_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5529_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5530_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_5531_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_h_x3f_5532_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_5533_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_xh_5534_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5535_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5536_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_5537_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_5538_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_5539_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___y_5540_: *mut leanh::LeanObject = *_args.add(21);
    let mut v___y_5541_: *mut leanh::LeanObject = *_args.add(22);
    let mut v___y_5542_: *mut leanh::LeanObject = *_args.add(23);
    let mut v___x_72185__boxed_5543_: u8 = 0;
    let mut v_res_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_72185__boxed_5543_ = (leanh::lean_unbox(v___x_5529_) as u8);
    v_res_5544_ = l_Lean_Elab_Do_elabDoFor___lam__9(
        v___x_5519_,
        v___x_5520_,
        v_x_5521_,
        v_a_5522_,
        v_a_5523_,
        v_u_5524_,
        v_snd_5525_,
        v___f_5526_,
        v___x_5527_,
        v_body_5528_,
        v___x_72185__boxed_5543_,
        v___y_5530_,
        v_a_5531_,
        v_h_x3f_5532_,
        v___x_5533_,
        v_xh_5534_,
        v___y_5535_,
        v___y_5536_,
        v___y_5537_,
        v___y_5538_,
        v___y_5539_,
        v___y_5540_,
        v___y_5541_,
    );
    leanh::lean_dec(v___y_5541_);
    leanh::lean_dec_ref(v___y_5540_);
    leanh::lean_dec(v___y_5539_);
    leanh::lean_dec_ref(v___y_5538_);
    leanh::lean_dec(v___y_5537_);
    leanh::lean_dec_ref(v___y_5536_);
    leanh::lean_dec_ref(v___y_5535_);
    leanh::lean_dec(v___x_5533_);
    leanh::lean_dec(v___x_5520_);
    leanh::lean_dec_ref(v___x_5519_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
    mut v_name_5545_: *mut leanh::LeanObject,
    mut v_type_5546_: *mut leanh::LeanObject,
    mut v_k_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5556_: u8 = 0;
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5556_ = 0;
    v___x_5557_ = 0;
    v___x_5558_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(
        v_name_5545_,
        v___x_5556_,
        v_type_5546_,
        v_k_5547_,
        v___x_5557_,
        v___y_5548_,
        v___y_5549_,
        v___y_5550_,
        v___y_5551_,
        v___y_5552_,
        v___y_5553_,
        v___y_5554_,
    );
    return v___x_5558_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg___boxed(
    mut v_name_5559_: *mut leanh::LeanObject,
    mut v_type_5560_: *mut leanh::LeanObject,
    mut v_k_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
    mut v___y_5567_: *mut leanh::LeanObject,
    mut v___y_5568_: *mut leanh::LeanObject,
    mut v___y_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5570_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
        v_name_5559_,
        v_type_5560_,
        v_k_5561_,
        v___y_5562_,
        v___y_5563_,
        v___y_5564_,
        v___y_5565_,
        v___y_5566_,
        v___y_5567_,
        v___y_5568_,
    );
    leanh::lean_dec(v___y_5568_);
    leanh::lean_dec_ref(v___y_5567_);
    leanh::lean_dec(v___y_5566_);
    leanh::lean_dec_ref(v___y_5565_);
    leanh::lean_dec(v___y_5564_);
    leanh::lean_dec_ref(v___y_5563_);
    leanh::lean_dec_ref(v___y_5562_);
    return v_res_5570_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__10(
    mut v_returnsEarly_5588_: u8,
    mut v_a_5589_: *mut leanh::LeanObject,
    mut v_a_5590_: *mut leanh::LeanObject,
    mut v_doBlockResultType_5591_: *mut leanh::LeanObject,
    mut v_a_5592_: *mut leanh::LeanObject,
    mut v_v_5593_: *mut leanh::LeanObject,
    mut v_u_5594_: *mut leanh::LeanObject,
    mut v___f_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___x_5597_: *mut leanh::LeanObject,
    mut v___x_5598_: *mut leanh::LeanObject,
    mut v___y_5599_: *mut leanh::LeanObject,
    mut v___y_5600_: *mut leanh::LeanObject,
    mut v___y_5601_: *mut leanh::LeanObject,
    mut v___y_5602_: *mut leanh::LeanObject,
    mut v___y_5603_: *mut leanh::LeanObject,
    mut v___y_5604_: *mut leanh::LeanObject,
    mut v___y_5605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ret_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5650_: u8 = 0;
    let mut v_reuseFailAlloc_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_unused_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_returnsEarly_5588_ == 0 {
                    leanh::lean_dec_ref(v___f_5595_);
                    leanh::lean_dec(v_u_5594_);
                    leanh::lean_dec(v_v_5593_);
                    leanh::lean_dec_ref(v_a_5592_);
                    leanh::lean_dec_ref(v_doBlockResultType_5591_);
                    leanh::lean_dec(v_a_5590_);
                    v___x_5662_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(
                        v_a_5589_,
                        v___y_5599_,
                        v___y_5600_,
                        v___y_5601_,
                        v___y_5602_,
                        v___y_5603_,
                        v___y_5604_,
                        v___y_5605_,
                    );
                    return v___x_5662_;
                } else {
                    v___x_5663_ = l_Lean_Meta_getFVarFromUserName(
                        v_a_5590_,
                        v___y_5602_,
                        v___y_5603_,
                        v___y_5604_,
                        v___y_5605_,
                    );
                    if leanh::lean_obj_tag(v___x_5663_) == 0 {
                        v_a_5664_ = leanh::lean_ctor_get(v___x_5663_, 0);
                        leanh::lean_inc(v_a_5664_);
                        leanh::lean_dec_ref_known(v___x_5663_, 1);
                        v___x_5665_ = lean_array_get_size(v___y_5596_);
                        v___x_5666_ = lean_nat_dec_eq(v___x_5665_, v___x_5597_);
                        if v___x_5666_ == 0 {
                            v_ret_5608_ = v_a_5664_;
                            v___y_5609_ = v___y_5599_;
                            v___y_5610_ = v___y_5600_;
                            v___y_5611_ = v___y_5601_;
                            v___y_5612_ = v___y_5602_;
                            v___y_5613_ = v___y_5603_;
                            v___y_5614_ = v___y_5604_;
                            v___y_5615_ = v___y_5605_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5667_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__9;
                            v___x_5668_ = lean_mk_empty_array_with_capacity(v___x_5598_);
                            v___x_5669_ = lean_array_push(v___x_5668_, v_a_5664_);
                            v___x_5670_ = l_Lean_Meta_mkAppM(
                                v___x_5667_,
                                v___x_5669_,
                                v___y_5602_,
                                v___y_5603_,
                                v___y_5604_,
                                v___y_5605_,
                            );
                            if leanh::lean_obj_tag(v___x_5670_) == 0 {
                                v_a_5671_ = leanh::lean_ctor_get(v___x_5670_, 0);
                                leanh::lean_inc(v_a_5671_);
                                leanh::lean_dec_ref_known(v___x_5670_, 1);
                                v_ret_5608_ = v_a_5671_;
                                v___y_5609_ = v___y_5599_;
                                v___y_5610_ = v___y_5600_;
                                v___y_5611_ = v___y_5601_;
                                v___y_5612_ = v___y_5602_;
                                v___y_5613_ = v___y_5603_;
                                v___y_5614_ = v___y_5604_;
                                v___y_5615_ = v___y_5605_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v___f_5595_);
                                leanh::lean_dec(v_u_5594_);
                                leanh::lean_dec(v_v_5593_);
                                leanh::lean_dec_ref(v_a_5592_);
                                leanh::lean_dec_ref(v_doBlockResultType_5591_);
                                leanh::lean_dec_ref(v_a_5589_);
                                return v___x_5670_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___f_5595_);
                        leanh::lean_dec(v_u_5594_);
                        leanh::lean_dec(v_v_5593_);
                        leanh::lean_dec_ref(v_a_5592_);
                        leanh::lean_dec_ref(v_doBlockResultType_5591_);
                        leanh::lean_dec_ref(v_a_5589_);
                        return v___x_5663_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_5615_);
                leanh::lean_inc_ref(v___y_5614_);
                leanh::lean_inc(v___y_5613_);
                leanh::lean_inc_ref(v___y_5612_);
                leanh::lean_inc_ref(v_ret_5608_);
                v___x_5616_ = lean_infer_type(
                    v_ret_5608_,
                    v___y_5612_,
                    v___y_5613_,
                    v___y_5614_,
                    v___y_5615_,
                );
                if leanh::lean_obj_tag(v___x_5616_) == 0 {
                    v_a_5617_ = leanh::lean_ctor_get(v___x_5616_, 0);
                    leanh::lean_inc(v_a_5617_);
                    leanh::lean_dec_ref_known(v___x_5616_, 1);
                    v___x_5618_ = l_Lean_Elab_Do_mkMonadApp(
                        v_doBlockResultType_5591_,
                        v___y_5609_,
                        v___y_5610_,
                        v___y_5611_,
                        v___y_5612_,
                        v___y_5613_,
                        v___y_5614_,
                        v___y_5615_,
                    );
                    if leanh::lean_obj_tag(v___x_5618_) == 0 {
                        v_a_5619_ = leanh::lean_ctor_get(v___x_5618_, 0);
                        leanh::lean_inc(v_a_5619_);
                        leanh::lean_dec_ref_known(v___x_5618_, 1);
                        v___x_5620_ = l_Lean_Elab_Do_DoElemCont_continueWithUnit(
                            v_a_5589_,
                            v___y_5609_,
                            v___y_5610_,
                            v___y_5611_,
                            v___y_5612_,
                            v___y_5613_,
                            v___y_5614_,
                            v___y_5615_,
                        );
                        if leanh::lean_obj_tag(v___x_5620_) == 0 {
                            v_a_5621_ = leanh::lean_ctor_get(v___x_5620_, 0);
                            leanh::lean_inc(v_a_5621_);
                            leanh::lean_dec_ref_known(v___x_5620_, 1);
                            v___x_5622_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__1;
                            v___x_5623_ =
                                l_Lean_Core_mkFreshUserName(v___x_5622_, v___y_5614_, v___y_5615_);
                            if leanh::lean_obj_tag(v___x_5623_) == 0 {
                                v_a_5624_ = leanh::lean_ctor_get(v___x_5623_, 0);
                                leanh::lean_inc(v_a_5624_);
                                leanh::lean_dec_ref_known(v___x_5623_, 1);
                                v_resultType_5625_ = leanh::lean_ctor_get(v_a_5592_, 0);
                                v_isSharedCheck_5652_ =
                                    (!leanh::lean_is_exclusive(v_a_5592_)) as u8;
                                if v_isSharedCheck_5652_ == 0 {
                                    v_unused_5653_ = leanh::lean_ctor_get(v_a_5592_, 1);
                                    leanh::lean_dec(v_unused_5653_);
                                    v___x_5627_ = v_a_5592_;
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_resultType_5625_);
                                    leanh::lean_dec(v_a_5592_);
                                    v___x_5627_ = leanh::lean_box(0);
                                    v_isShared_5628_ = v_isSharedCheck_5652_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5621_);
                                leanh::lean_dec(v_a_5619_);
                                leanh::lean_dec(v_a_5617_);
                                leanh::lean_dec_ref(v_ret_5608_);
                                leanh::lean_dec_ref(v___f_5595_);
                                leanh::lean_dec(v_u_5594_);
                                leanh::lean_dec(v_v_5593_);
                                leanh::lean_dec_ref(v_a_5592_);
                                v_a_5654_ = leanh::lean_ctor_get(v___x_5623_, 0);
                                v_isSharedCheck_5661_ =
                                    (!leanh::lean_is_exclusive(v___x_5623_)) as u8;
                                if v_isSharedCheck_5661_ == 0 {
                                    v___x_5656_ = v___x_5623_;
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5654_);
                                    leanh::lean_dec(v___x_5623_);
                                    v___x_5656_ = leanh::lean_box(0);
                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5619_);
                            leanh::lean_dec(v_a_5617_);
                            leanh::lean_dec_ref(v_ret_5608_);
                            leanh::lean_dec_ref(v___f_5595_);
                            leanh::lean_dec(v_u_5594_);
                            leanh::lean_dec(v_v_5593_);
                            leanh::lean_dec_ref(v_a_5592_);
                            return v___x_5620_;
                        }
                    } else {
                        leanh::lean_dec(v_a_5617_);
                        leanh::lean_dec_ref(v_ret_5608_);
                        leanh::lean_dec_ref(v___f_5595_);
                        leanh::lean_dec(v_u_5594_);
                        leanh::lean_dec(v_v_5593_);
                        leanh::lean_dec_ref(v_a_5592_);
                        leanh::lean_dec_ref(v_a_5589_);
                        return v___x_5618_;
                    }
                } else {
                    leanh::lean_dec_ref(v_ret_5608_);
                    leanh::lean_dec_ref(v___f_5595_);
                    leanh::lean_dec(v_u_5594_);
                    leanh::lean_dec(v_v_5593_);
                    leanh::lean_dec_ref(v_a_5592_);
                    leanh::lean_dec_ref(v_doBlockResultType_5591_);
                    leanh::lean_dec_ref(v_a_5589_);
                    return v___x_5616_;
                }
            }
            2 => {
                v___x_5629_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__2;
                v___x_5630_ = 0;
                v___x_5631_ = l_Lean_mkLambda(v___x_5629_, v___x_5630_, v_a_5617_, v_a_5619_);
                v___x_5632_ = l_Lean_Elab_Do_elabDoFor___lam__10___closed__6;
                v___x_5633_ = l_Lean_Level_succ___override(v_v_5593_);
                v___x_5634_ = leanh::lean_box(0);
                if v_isShared_5628_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5627_, 1);
                    leanh::lean_ctor_set(v___x_5627_, 1, v___x_5634_);
                    leanh::lean_ctor_set(v___x_5627_, 0, v___x_5633_);
                    v___x_5636_ = v___x_5627_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5633_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___x_5634_);
                    v___x_5636_ = v_reuseFailAlloc_5651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5637_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5637_, 0, v_u_5594_);
                leanh::lean_ctor_set(v___x_5637_, 1, v___x_5636_);
                v___x_5638_ = l_Lean_mkConst(v___x_5632_, v___x_5637_);
                leanh::lean_inc_ref(v_resultType_5625_);
                v___x_5639_ =
                    l_Lean_mkApp3(v___x_5638_, v_resultType_5625_, v___x_5631_, v_ret_5608_);
                v___x_5640_ =
                    l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
                        v_a_5624_,
                        v_resultType_5625_,
                        v___f_5595_,
                        v___y_5609_,
                        v___y_5610_,
                        v___y_5611_,
                        v___y_5612_,
                        v___y_5613_,
                        v___y_5614_,
                        v___y_5615_,
                    );
                if leanh::lean_obj_tag(v___x_5640_) == 0 {
                    v_a_5641_ = leanh::lean_ctor_get(v___x_5640_, 0);
                    v_isSharedCheck_5650_ = (!leanh::lean_is_exclusive(v___x_5640_)) as u8;
                    if v_isSharedCheck_5650_ == 0 {
                        v___x_5643_ = v___x_5640_;
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5641_);
                        leanh::lean_dec(v___x_5640_);
                        v___x_5643_ = leanh::lean_box(0);
                        v_isShared_5644_ = v_isSharedCheck_5650_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5639_);
                    leanh::lean_dec(v_a_5621_);
                    return v___x_5640_;
                }
            }
            4 => {
                v___x_5645_ = l_Lean_mkSimpleThunk(v_a_5621_);
                v___x_5646_ = l_Lean_mkAppB(v___x_5639_, v_a_5641_, v___x_5645_);
                if v_isShared_5644_ == 0 {
                    leanh::lean_ctor_set(v___x_5643_, 0, v___x_5646_);
                    v___x_5648_ = v___x_5643_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5646_);
                    v___x_5648_ = v_reuseFailAlloc_5649_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5648_;
            }
            6 => {
                if v_isShared_5657_ == 0 {
                    v___x_5659_ = v___x_5656_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
                    v___x_5659_ = v_reuseFailAlloc_5660_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__10___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_returnsEarly_5672_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_a_5673_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_5674_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_doBlockResultType_5675_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_5676_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_v_5677_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_u_5678_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_5679_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5680_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_5681_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5682_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5683_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5684_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5685_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5686_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5687_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5688_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5689_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_5690_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_returnsEarly_boxed_5691_: u8 = 0;
    let mut v_res_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_returnsEarly_boxed_5691_ = (leanh::lean_unbox(v_returnsEarly_5672_) as u8);
    v_res_5692_ = l_Lean_Elab_Do_elabDoFor___lam__10(
        v_returnsEarly_boxed_5691_,
        v_a_5673_,
        v_a_5674_,
        v_doBlockResultType_5675_,
        v_a_5676_,
        v_v_5677_,
        v_u_5678_,
        v___f_5679_,
        v___y_5680_,
        v___x_5681_,
        v___x_5682_,
        v___y_5683_,
        v___y_5684_,
        v___y_5685_,
        v___y_5686_,
        v___y_5687_,
        v___y_5688_,
        v___y_5689_,
    );
    leanh::lean_dec(v___y_5689_);
    leanh::lean_dec_ref(v___y_5688_);
    leanh::lean_dec(v___y_5687_);
    leanh::lean_dec_ref(v___y_5686_);
    leanh::lean_dec(v___y_5685_);
    leanh::lean_dec_ref(v___y_5684_);
    leanh::lean_dec_ref(v___y_5683_);
    leanh::lean_dec(v___x_5682_);
    leanh::lean_dec(v___x_5681_);
    leanh::lean_dec_ref(v___y_5680_);
    return v_res_5692_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11(
    mut v___y_5693_: *mut leanh::LeanObject,
    mut v___y_5694_: *mut leanh::LeanObject,
    mut v___x_5695_: *mut leanh::LeanObject,
    mut v___x_5696_: u8,
    mut v_postS_5697_: *mut leanh::LeanObject,
    mut v___y_5698_: *mut leanh::LeanObject,
    mut v___y_5699_: *mut leanh::LeanObject,
    mut v___y_5700_: *mut leanh::LeanObject,
    mut v___y_5701_: *mut leanh::LeanObject,
    mut v___y_5702_: *mut leanh::LeanObject,
    mut v___y_5703_: *mut leanh::LeanObject,
    mut v___y_5704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5706_ = l_Lean_Expr_fvarId_x21(v_postS_5697_);
    v___x_5707_ = l_Lean_Elab_Do_bindMutVarsFromTuple(
        v___y_5693_,
        v___x_5706_,
        v___y_5694_,
        v___y_5698_,
        v___y_5699_,
        v___y_5700_,
        v___y_5701_,
        v___y_5702_,
        v___y_5703_,
        v___y_5704_,
    );
    if leanh::lean_obj_tag(v___x_5707_) == 0 {
        let mut v_a_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5711_: u8 = 0;
        let mut v___x_5712_: u8 = 0;
        let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_5708_ = leanh::lean_ctor_get(v___x_5707_, 0);
        leanh::lean_inc(v_a_5708_);
        leanh::lean_dec_ref_known(v___x_5707_, 1);
        v___x_5709_ = lean_mk_empty_array_with_capacity(v___x_5695_);
        v___x_5710_ = lean_array_push(v___x_5709_, v_postS_5697_);
        v___x_5711_ = 0;
        v___x_5712_ = 1;
        v___x_5713_ = l_Lean_Meta_mkLambdaFVars(
            v___x_5710_,
            v_a_5708_,
            v___x_5711_,
            v___x_5696_,
            v___x_5711_,
            v___x_5696_,
            v___x_5712_,
            v___y_5701_,
            v___y_5702_,
            v___y_5703_,
            v___y_5704_,
        );
        leanh::lean_dec_ref(v___x_5710_);
        return v___x_5713_;
    } else {
        leanh::lean_dec_ref(v_postS_5697_);
        return v___x_5707_;
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__11___boxed(
    mut v___y_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
    mut v___x_5716_: *mut leanh::LeanObject,
    mut v___x_5717_: *mut leanh::LeanObject,
    mut v_postS_5718_: *mut leanh::LeanObject,
    mut v___y_5719_: *mut leanh::LeanObject,
    mut v___y_5720_: *mut leanh::LeanObject,
    mut v___y_5721_: *mut leanh::LeanObject,
    mut v___y_5722_: *mut leanh::LeanObject,
    mut v___y_5723_: *mut leanh::LeanObject,
    mut v___y_5724_: *mut leanh::LeanObject,
    mut v___y_5725_: *mut leanh::LeanObject,
    mut v___y_5726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_72567__boxed_5727_: u8 = 0;
    let mut v_res_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_72567__boxed_5727_ = (leanh::lean_unbox(v___x_5717_) as u8);
    v_res_5728_ = l_Lean_Elab_Do_elabDoFor___lam__11(
        v___y_5714_,
        v___y_5715_,
        v___x_5716_,
        v___x_72567__boxed_5727_,
        v_postS_5718_,
        v___y_5719_,
        v___y_5720_,
        v___y_5721_,
        v___y_5722_,
        v___y_5723_,
        v___y_5724_,
        v___y_5725_,
    );
    leanh::lean_dec(v___y_5725_);
    leanh::lean_dec_ref(v___y_5724_);
    leanh::lean_dec(v___y_5723_);
    leanh::lean_dec_ref(v___y_5722_);
    leanh::lean_dec(v___y_5721_);
    leanh::lean_dec_ref(v___y_5720_);
    leanh::lean_dec_ref(v___y_5719_);
    leanh::lean_dec(v___x_5716_);
    return v_res_5728_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12(
    mut v_a_5734_: *mut leanh::LeanObject,
    mut v_a_5735_: *mut leanh::LeanObject,
    mut v___x_5736_: *mut leanh::LeanObject,
    mut v_a_5737_: *mut leanh::LeanObject,
    mut v_a_5738_: *mut leanh::LeanObject,
    mut v_val_5739_: *mut leanh::LeanObject,
    mut v_a_5740_: *mut leanh::LeanObject,
    mut v_x_5741_: *mut leanh::LeanObject,
    mut v___y_5742_: *mut leanh::LeanObject,
    mut v___y_5743_: *mut leanh::LeanObject,
    mut v___y_5744_: *mut leanh::LeanObject,
    mut v___y_5745_: *mut leanh::LeanObject,
    mut v___y_5746_: *mut leanh::LeanObject,
    mut v___y_5747_: *mut leanh::LeanObject,
    mut v___y_5748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_Elab_Do_elabDoFor___lam__12___closed__2;
    v___x_5751_ = leanh::lean_box(0);
    v___x_5752_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5752_, 0, v_a_5734_);
    leanh::lean_ctor_set(v___x_5752_, 1, v___x_5751_);
    v___x_5753_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5753_, 0, v_a_5735_);
    leanh::lean_ctor_set(v___x_5753_, 1, v___x_5752_);
    v___x_5754_ = l_Lean_mkConst(v___x_5750_, v___x_5753_);
    v___x_5755_ = l_Lean_instInhabitedExpr;
    v___x_5756_ = lean_array_get_borrowed(v___x_5755_, v_x_5741_, v___x_5736_);
    leanh::lean_inc(v___x_5756_);
    v___x_5757_ = l_Lean_mkApp5(
        v___x_5754_,
        v_a_5737_,
        v_a_5738_,
        v_val_5739_,
        v_a_5740_,
        v___x_5756_,
    );
    v___x_5758_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5758_, 0, v___x_5757_);
    return v___x_5758_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___lam__12___boxed(
    mut v_a_5759_: *mut leanh::LeanObject,
    mut v_a_5760_: *mut leanh::LeanObject,
    mut v___x_5761_: *mut leanh::LeanObject,
    mut v_a_5762_: *mut leanh::LeanObject,
    mut v_a_5763_: *mut leanh::LeanObject,
    mut v_val_5764_: *mut leanh::LeanObject,
    mut v_a_5765_: *mut leanh::LeanObject,
    mut v_x_5766_: *mut leanh::LeanObject,
    mut v___y_5767_: *mut leanh::LeanObject,
    mut v___y_5768_: *mut leanh::LeanObject,
    mut v___y_5769_: *mut leanh::LeanObject,
    mut v___y_5770_: *mut leanh::LeanObject,
    mut v___y_5771_: *mut leanh::LeanObject,
    mut v___y_5772_: *mut leanh::LeanObject,
    mut v___y_5773_: *mut leanh::LeanObject,
    mut v___y_5774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5775_ = l_Lean_Elab_Do_elabDoFor___lam__12(
        v_a_5759_,
        v_a_5760_,
        v___x_5761_,
        v_a_5762_,
        v_a_5763_,
        v_val_5764_,
        v_a_5765_,
        v_x_5766_,
        v___y_5767_,
        v___y_5768_,
        v___y_5769_,
        v___y_5770_,
        v___y_5771_,
        v___y_5772_,
        v___y_5773_,
    );
    leanh::lean_dec(v___y_5773_);
    leanh::lean_dec_ref(v___y_5772_);
    leanh::lean_dec(v___y_5771_);
    leanh::lean_dec_ref(v___y_5770_);
    leanh::lean_dec(v___y_5769_);
    leanh::lean_dec_ref(v___y_5768_);
    leanh::lean_dec_ref(v___y_5767_);
    leanh::lean_dec_ref(v_x_5766_);
    leanh::lean_dec(v___x_5761_);
    return v_res_5775_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(
    mut v_a_5776_: *mut leanh::LeanObject,
    mut v_as_5777_: *mut leanh::LeanObject,
    mut v_i_5778_: usize,
    mut v_stop_5779_: usize,
    mut v_b_5780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5786_: u8 = 0;
    let mut v_reassigns_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5786_ = lean_usize_dec_eq(v_i_5778_, v_stop_5779_);
                if v___x_5786_ == 0 {
                    v_reassigns_5787_ = leanh::lean_ctor_get(v_a_5776_, 1);
                    v___x_5788_ = lean_array_uget_borrowed(v_as_5777_, v_i_5778_);
                    v___x_5789_ = l_Lean_TSyntax_getId(v___x_5788_);
                    v___x_5790_ = l_Lean_NameSet_contains(v_reassigns_5787_, v___x_5789_);
                    leanh::lean_dec(v___x_5789_);
                    if v___x_5790_ == 0 {
                        v___y_5782_ = v_b_5780_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_5788_);
                        v___x_5791_ = lean_array_push(v_b_5780_, v___x_5788_);
                        v___y_5782_ = v___x_5791_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5780_;
                }
            }
            1 => {
                v___x_5783_ = 1usize;
                v___x_5784_ = lean_usize_add(v_i_5778_, v___x_5783_);
                v_i_5778_ = v___x_5784_;
                v_b_5780_ = v___y_5782_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7___boxed(
    mut v_a_5792_: *mut leanh::LeanObject,
    mut v_as_5793_: *mut leanh::LeanObject,
    mut v_i_5794_: *mut leanh::LeanObject,
    mut v_stop_5795_: *mut leanh::LeanObject,
    mut v_b_5796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5797_: usize = 0;
    let mut v_stop_boxed_5798_: usize = 0;
    let mut v_res_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5797_ = leanh::lean_unbox_usize(v_i_5794_);
    leanh::lean_dec(v_i_5794_);
    v_stop_boxed_5798_ = leanh::lean_unbox_usize(v_stop_5795_);
    leanh::lean_dec(v_stop_5795_);
    v_res_5799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_5792_, v_as_5793_, v_i_boxed_5797_, v_stop_boxed_5798_, v_b_5796_);
    leanh::lean_dec_ref(v_as_5793_);
    leanh::lean_dec_ref(v_a_5792_);
    return v_res_5799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(
    mut v_sz_5800_: usize,
    mut v_i_5801_: usize,
    mut v_bs_5802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5803_: u8 = 0;
    let mut v_v_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: usize = 0;
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5803_ = lean_usize_dec_lt(v_i_5801_, v_sz_5800_);
                if v___x_5803_ == 0 {
                    return v_bs_5802_;
                } else {
                    v_v_5804_ = lean_array_uget(v_bs_5802_, v_i_5801_);
                    v___x_5805_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5806_ = lean_array_uset(v_bs_5802_, v_i_5801_, v___x_5805_);
                    v___x_5807_ = l_Lean_TSyntax_getId(v_v_5804_);
                    leanh::lean_dec(v_v_5804_);
                    v___x_5808_ = 1usize;
                    v___x_5809_ = lean_usize_add(v_i_5801_, v___x_5808_);
                    v___x_5810_ = lean_array_uset(v_bs_x27_5806_, v_i_5801_, v___x_5807_);
                    v_i_5801_ = v___x_5809_;
                    v_bs_5802_ = v___x_5810_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6___boxed(
    mut v_sz_5812_: *mut leanh::LeanObject,
    mut v_i_5813_: *mut leanh::LeanObject,
    mut v_bs_5814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5815_: usize = 0;
    let mut v_i_boxed_5816_: usize = 0;
    let mut v_res_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5815_ = leanh::lean_unbox_usize(v_sz_5812_);
    leanh::lean_dec(v_sz_5812_);
    v_i_boxed_5816_ = leanh::lean_unbox_usize(v_i_5813_);
    leanh::lean_dec(v_i_5813_);
    v_res_5817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_boxed_5815_, v_i_boxed_5816_, v_bs_5814_);
    return v_res_5817_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(
    mut v___x_5818_: *mut leanh::LeanObject,
    mut v_a_5819_: *mut leanh::LeanObject,
    mut v___y_5820_: *mut leanh::LeanObject,
    mut v___y_5821_: *mut leanh::LeanObject,
    mut v___y_5822_: *mut leanh::LeanObject,
    mut v___y_5823_: *mut leanh::LeanObject,
    mut v___y_5824_: *mut leanh::LeanObject,
    mut v___y_5825_: *mut leanh::LeanObject,
    mut v___y_5826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70870__overap_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_instInhabitedExpr;
    v___x_70870__overap_5829_ = l_instInhabitedOfMonad___redArg(v___x_5818_, v___x_5828_);
    leanh::lean_inc(v___y_5826_);
    leanh::lean_inc_ref(v___y_5825_);
    leanh::lean_inc(v___y_5824_);
    leanh::lean_inc_ref(v___y_5823_);
    leanh::lean_inc(v___y_5822_);
    leanh::lean_inc_ref(v___y_5821_);
    leanh::lean_inc_ref(v___y_5820_);
    v___x_5830_ = leanh::lean_apply_8(
        v___x_70870__overap_5829_,
        v___y_5820_,
        v___y_5821_,
        v___y_5822_,
        v___y_5823_,
        v___y_5824_,
        v___y_5825_,
        v___y_5826_,
        leanh::lean_box(0),
    );
    return v___x_5830_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed(
    mut v___x_5831_: *mut leanh::LeanObject,
    mut v_a_5832_: *mut leanh::LeanObject,
    mut v___y_5833_: *mut leanh::LeanObject,
    mut v___y_5834_: *mut leanh::LeanObject,
    mut v___y_5835_: *mut leanh::LeanObject,
    mut v___y_5836_: *mut leanh::LeanObject,
    mut v___y_5837_: *mut leanh::LeanObject,
    mut v___y_5838_: *mut leanh::LeanObject,
    mut v___y_5839_: *mut leanh::LeanObject,
    mut v___y_5840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0(v___x_5831_, v_a_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
    leanh::lean_dec(v___y_5839_);
    leanh::lean_dec_ref(v___y_5838_);
    leanh::lean_dec(v___y_5837_);
    leanh::lean_dec_ref(v___y_5836_);
    leanh::lean_dec(v___y_5835_);
    leanh::lean_dec_ref(v___y_5834_);
    leanh::lean_dec_ref(v___y_5833_);
    leanh::lean_dec_ref(v_a_5832_);
    return v_res_5841_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5842_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_5842_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__0);
    v___x_5844_ = l_StateRefT_x27_instMonad___redArg(v___x_5843_);
    return v___x_5844_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed(
    mut v_acc_5851_: *mut leanh::LeanObject,
    mut v_declInfos_5852_: *mut leanh::LeanObject,
    mut v_k_5853_: *mut leanh::LeanObject,
    mut v_kind_5854_: *mut leanh::LeanObject,
    mut v_x_5855_: *mut leanh::LeanObject,
    mut v___y_5856_: *mut leanh::LeanObject,
    mut v___y_5857_: *mut leanh::LeanObject,
    mut v___y_5858_: *mut leanh::LeanObject,
    mut v___y_5859_: *mut leanh::LeanObject,
    mut v___y_5860_: *mut leanh::LeanObject,
    mut v___y_5861_: *mut leanh::LeanObject,
    mut v___y_5862_: *mut leanh::LeanObject,
    mut v___y_5863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_5864_: u8 = 0;
    let mut v_res_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5864_ = (leanh::lean_unbox(v_kind_5854_) as u8);
    v_res_5865_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(v_acc_5851_, v_declInfos_5852_, v_k_5853_, v_kind_boxed_5864_, v_x_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_, v___y_5862_);
    leanh::lean_dec(v___y_5862_);
    leanh::lean_dec_ref(v___y_5861_);
    leanh::lean_dec(v___y_5860_);
    leanh::lean_dec_ref(v___y_5859_);
    leanh::lean_dec(v___y_5858_);
    leanh::lean_dec_ref(v___y_5857_);
    leanh::lean_dec_ref(v___y_5856_);
    return v_res_5865_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(
    mut v_declInfos_5866_: *mut leanh::LeanObject,
    mut v_k_5867_: *mut leanh::LeanObject,
    mut v_kind_5868_: u8,
    mut v_acc_5869_: *mut leanh::LeanObject,
    mut v___y_5870_: *mut leanh::LeanObject,
    mut v___y_5871_: *mut leanh::LeanObject,
    mut v___y_5872_: *mut leanh::LeanObject,
    mut v___y_5873_: *mut leanh::LeanObject,
    mut v___y_5874_: *mut leanh::LeanObject,
    mut v___y_5875_: *mut leanh::LeanObject,
    mut v___y_5876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5898_: u8 = 0;
    let mut v_toFunctor_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5905_: u8 = 0;
    let mut v___f_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v_toFunctor_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5929_: u8 = 0;
    let mut v___f_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___f_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut v_unused_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v_unused_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_unused_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5975_: u8 = 0;
    let mut v_unused_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5878_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__1);
                v_toApplicative_5879_ = leanh::lean_ctor_get(v___x_5878_, 0);
                v_toFunctor_5880_ = leanh::lean_ctor_get(v_toApplicative_5879_, 0);
                v_toSeq_5881_ = leanh::lean_ctor_get(v_toApplicative_5879_, 2);
                v_toSeqLeft_5882_ = leanh::lean_ctor_get(v_toApplicative_5879_, 3);
                v_toSeqRight_5883_ = leanh::lean_ctor_get(v_toApplicative_5879_, 4);
                v___f_5884_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__2;
                v___f_5885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_5880_, 2);
                v___f_5886_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5886_, 0, v_toFunctor_5880_);
                v___f_5887_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5887_, 0, v_toFunctor_5880_);
                v___x_5888_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5888_, 0, v___f_5886_);
                leanh::lean_ctor_set(v___x_5888_, 1, v___f_5887_);
                leanh::lean_inc(v_toSeqRight_5883_);
                v___f_5889_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5889_, 0, v_toSeqRight_5883_);
                leanh::lean_inc(v_toSeqLeft_5882_);
                v___f_5890_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5890_, 0, v_toSeqLeft_5882_);
                leanh::lean_inc(v_toSeq_5881_);
                v___f_5891_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5891_, 0, v_toSeq_5881_);
                v___x_5892_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5892_, 0, v___x_5888_);
                leanh::lean_ctor_set(v___x_5892_, 1, v___f_5884_);
                leanh::lean_ctor_set(v___x_5892_, 2, v___f_5891_);
                leanh::lean_ctor_set(v___x_5892_, 3, v___f_5890_);
                leanh::lean_ctor_set(v___x_5892_, 4, v___f_5889_);
                v___x_5893_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5893_, 0, v___x_5892_);
                leanh::lean_ctor_set(v___x_5893_, 1, v___f_5885_);
                v___x_5894_ = l_StateRefT_x27_instMonad___redArg(v___x_5893_);
                v_toApplicative_5895_ = leanh::lean_ctor_get(v___x_5894_, 0);
                v_isSharedCheck_5975_ = (!leanh::lean_is_exclusive(v___x_5894_)) as u8;
                if v_isSharedCheck_5975_ == 0 {
                    v_unused_5976_ = leanh::lean_ctor_get(v___x_5894_, 1);
                    leanh::lean_dec(v_unused_5976_);
                    v___x_5897_ = v___x_5894_;
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_5895_);
                    leanh::lean_dec(v___x_5894_);
                    v___x_5897_ = leanh::lean_box(0);
                    v_isShared_5898_ = v_isSharedCheck_5975_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5899_ = leanh::lean_ctor_get(v_toApplicative_5895_, 0);
                v_toSeq_5900_ = leanh::lean_ctor_get(v_toApplicative_5895_, 2);
                v_toSeqLeft_5901_ = leanh::lean_ctor_get(v_toApplicative_5895_, 3);
                v_toSeqRight_5902_ = leanh::lean_ctor_get(v_toApplicative_5895_, 4);
                v_isSharedCheck_5973_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_5895_)) as u8;
                if v_isSharedCheck_5973_ == 0 {
                    v_unused_5974_ = leanh::lean_ctor_get(v_toApplicative_5895_, 1);
                    leanh::lean_dec(v_unused_5974_);
                    v___x_5904_ = v_toApplicative_5895_;
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_5902_);
                    leanh::lean_inc(v_toSeqLeft_5901_);
                    leanh::lean_inc(v_toSeq_5900_);
                    leanh::lean_inc(v_toFunctor_5899_);
                    leanh::lean_dec(v_toApplicative_5895_);
                    v___x_5904_ = leanh::lean_box(0);
                    v_isShared_5905_ = v_isSharedCheck_5973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5906_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__4;
                v___f_5907_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__5;
                leanh::lean_inc_ref(v_toFunctor_5899_);
                v___f_5908_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5908_, 0, v_toFunctor_5899_);
                v___f_5909_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5909_, 0, v_toFunctor_5899_);
                v___x_5910_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5910_, 0, v___f_5908_);
                leanh::lean_ctor_set(v___x_5910_, 1, v___f_5909_);
                v___f_5911_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5911_, 0, v_toSeqRight_5902_);
                v___f_5912_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5912_, 0, v_toSeqLeft_5901_);
                v___f_5913_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5913_, 0, v_toSeq_5900_);
                if v_isShared_5905_ == 0 {
                    leanh::lean_ctor_set(v___x_5904_, 4, v___f_5911_);
                    leanh::lean_ctor_set(v___x_5904_, 3, v___f_5912_);
                    leanh::lean_ctor_set(v___x_5904_, 2, v___f_5913_);
                    leanh::lean_ctor_set(v___x_5904_, 1, v___f_5906_);
                    leanh::lean_ctor_set(v___x_5904_, 0, v___x_5910_);
                    v___x_5915_ = v___x_5904_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5972_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___f_5906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 2, v___f_5913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 3, v___f_5912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5972_, 4, v___f_5911_);
                    v___x_5915_ = v_reuseFailAlloc_5972_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5898_ == 0 {
                    leanh::lean_ctor_set(v___x_5897_, 1, v___f_5907_);
                    leanh::lean_ctor_set(v___x_5897_, 0, v___x_5915_);
                    v___x_5917_ = v___x_5897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5971_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___f_5907_);
                    v___x_5917_ = v_reuseFailAlloc_5971_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5918_ = l_StateRefT_x27_instMonad___redArg(v___x_5917_);
                v_toApplicative_5919_ = leanh::lean_ctor_get(v___x_5918_, 0);
                v_isSharedCheck_5969_ = (!leanh::lean_is_exclusive(v___x_5918_)) as u8;
                if v_isSharedCheck_5969_ == 0 {
                    v_unused_5970_ = leanh::lean_ctor_get(v___x_5918_, 1);
                    leanh::lean_dec(v_unused_5970_);
                    v___x_5921_ = v___x_5918_;
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_5919_);
                    leanh::lean_dec(v___x_5918_);
                    v___x_5921_ = leanh::lean_box(0);
                    v_isShared_5922_ = v_isSharedCheck_5969_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_5923_ = leanh::lean_ctor_get(v_toApplicative_5919_, 0);
                v_toSeq_5924_ = leanh::lean_ctor_get(v_toApplicative_5919_, 2);
                v_toSeqLeft_5925_ = leanh::lean_ctor_get(v_toApplicative_5919_, 3);
                v_toSeqRight_5926_ = leanh::lean_ctor_get(v_toApplicative_5919_, 4);
                v_isSharedCheck_5967_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_5919_)) as u8;
                if v_isSharedCheck_5967_ == 0 {
                    v_unused_5968_ = leanh::lean_ctor_get(v_toApplicative_5919_, 1);
                    leanh::lean_dec(v_unused_5968_);
                    v___x_5928_ = v_toApplicative_5919_;
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_5926_);
                    leanh::lean_inc(v_toSeqLeft_5925_);
                    leanh::lean_inc(v_toSeq_5924_);
                    leanh::lean_inc(v_toFunctor_5923_);
                    leanh::lean_dec(v_toApplicative_5919_);
                    v___x_5928_ = leanh::lean_box(0);
                    v_isShared_5929_ = v_isSharedCheck_5967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_5930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__6;
                v___f_5931_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___closed__7;
                leanh::lean_inc_ref(v_toFunctor_5923_);
                v___f_5932_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5932_, 0, v_toFunctor_5923_);
                v___f_5933_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5933_, 0, v_toFunctor_5923_);
                v___x_5934_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5934_, 0, v___f_5932_);
                leanh::lean_ctor_set(v___x_5934_, 1, v___f_5933_);
                v___f_5935_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5935_, 0, v_toSeqRight_5926_);
                v___f_5936_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5936_, 0, v_toSeqLeft_5925_);
                v___f_5937_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_5937_, 0, v_toSeq_5924_);
                if v_isShared_5929_ == 0 {
                    leanh::lean_ctor_set(v___x_5928_, 4, v___f_5935_);
                    leanh::lean_ctor_set(v___x_5928_, 3, v___f_5936_);
                    leanh::lean_ctor_set(v___x_5928_, 2, v___f_5937_);
                    leanh::lean_ctor_set(v___x_5928_, 1, v___f_5930_);
                    leanh::lean_ctor_set(v___x_5928_, 0, v___x_5934_);
                    v___x_5939_ = v___x_5928_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5966_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5934_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 1, v___f_5930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 2, v___f_5937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 3, v___f_5936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 4, v___f_5935_);
                    v___x_5939_ = v_reuseFailAlloc_5966_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5922_ == 0 {
                    leanh::lean_ctor_set(v___x_5921_, 1, v___f_5931_);
                    leanh::lean_ctor_set(v___x_5921_, 0, v___x_5939_);
                    v___x_5941_ = v___x_5921_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5965_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 0, v___x_5939_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5965_, 1, v___f_5931_);
                    v___x_5941_ = v_reuseFailAlloc_5965_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5942_ = l_ReaderT_instMonad___redArg(v___x_5941_);
                v___x_5943_ = lean_array_get_size(v_acc_5869_);
                v___x_5944_ = lean_array_get_size(v_declInfos_5866_);
                v___x_5945_ = lean_nat_dec_lt(v___x_5943_, v___x_5944_);
                if v___x_5945_ == 0 {
                    leanh::lean_dec_ref(v___x_5942_);
                    leanh::lean_dec_ref(v_declInfos_5866_);
                    leanh::lean_inc(v___y_5876_);
                    leanh::lean_inc_ref(v___y_5875_);
                    leanh::lean_inc(v___y_5874_);
                    leanh::lean_inc_ref(v___y_5873_);
                    leanh::lean_inc(v___y_5872_);
                    leanh::lean_inc_ref(v___y_5871_);
                    leanh::lean_inc_ref(v___y_5870_);
                    v___x_5946_ = leanh::lean_apply_9(
                        v_k_5867_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        leanh::lean_box(0),
                    );
                    return v___x_5946_;
                } else {
                    v___f_5947_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    leanh::lean_closure_set(v___f_5947_, 0, v___x_5942_);
                    v___x_5948_ = leanh::lean_box(0);
                    v___x_5949_ = 0;
                    v___f_5950_ = leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5950_, 0, v___f_5947_);
                    v___x_5951_ = leanh::lean_box((v___x_5949_) as usize);
                    v___x_5952_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5952_, 0, v___x_5951_);
                    leanh::lean_ctor_set(v___x_5952_, 1, v___f_5950_);
                    v___x_5953_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5953_, 0, v___x_5948_);
                    leanh::lean_ctor_set(v___x_5953_, 1, v___x_5952_);
                    v___x_5954_ = lean_array_get(v___x_5953_, v_declInfos_5866_, v___x_5943_);
                    leanh::lean_dec_ref_known(v___x_5953_, 2);
                    v_snd_5955_ = leanh::lean_ctor_get(v___x_5954_, 1);
                    leanh::lean_inc(v_snd_5955_);
                    v_fst_5956_ = leanh::lean_ctor_get(v___x_5954_, 0);
                    leanh::lean_inc(v_fst_5956_);
                    leanh::lean_dec(v___x_5954_);
                    v_fst_5957_ = leanh::lean_ctor_get(v_snd_5955_, 0);
                    leanh::lean_inc(v_fst_5957_);
                    v_snd_5958_ = leanh::lean_ctor_get(v_snd_5955_, 1);
                    leanh::lean_inc(v_snd_5958_);
                    leanh::lean_dec(v_snd_5955_);
                    leanh::lean_inc(v___y_5876_);
                    leanh::lean_inc_ref(v___y_5875_);
                    leanh::lean_inc(v___y_5874_);
                    leanh::lean_inc_ref(v___y_5873_);
                    leanh::lean_inc(v___y_5872_);
                    leanh::lean_inc_ref(v___y_5871_);
                    leanh::lean_inc_ref(v___y_5870_);
                    leanh::lean_inc_ref(v_acc_5869_);
                    v___x_5959_ = leanh::lean_apply_9(
                        v_snd_5958_,
                        v_acc_5869_,
                        v___y_5870_,
                        v___y_5871_,
                        v___y_5872_,
                        v___y_5873_,
                        v___y_5874_,
                        v___y_5875_,
                        v___y_5876_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_5959_) == 0 {
                        v_a_5960_ = leanh::lean_ctor_get(v___x_5959_, 0);
                        leanh::lean_inc(v_a_5960_);
                        leanh::lean_dec_ref_known(v___x_5959_, 1);
                        v___x_5961_ = leanh::lean_box((v_kind_5868_) as usize);
                        v___f_5962_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1___boxed as *mut core::ffi::c_void, 13, 4);
                        leanh::lean_closure_set(v___f_5962_, 0, v_acc_5869_);
                        leanh::lean_closure_set(v___f_5962_, 1, v_declInfos_5866_);
                        leanh::lean_closure_set(v___f_5962_, 2, v_k_5867_);
                        leanh::lean_closure_set(v___f_5962_, 3, v___x_5961_);
                        v___x_5963_ = (leanh::lean_unbox(v_fst_5957_) as u8);
                        leanh::lean_dec(v_fst_5957_);
                        v___x_5964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Elab_Do_elabDoFor_spec__3___redArg(v_fst_5956_, v___x_5963_, v_a_5960_, v___f_5962_, v_kind_5868_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                        return v___x_5964_;
                    } else {
                        leanh::lean_dec(v_fst_5957_);
                        leanh::lean_dec(v_fst_5956_);
                        leanh::lean_dec_ref(v_acc_5869_);
                        leanh::lean_dec_ref(v_k_5867_);
                        leanh::lean_dec_ref(v_declInfos_5866_);
                        return v___x_5959_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___lam__1(
    mut v_acc_5977_: *mut leanh::LeanObject,
    mut v_declInfos_5978_: *mut leanh::LeanObject,
    mut v_k_5979_: *mut leanh::LeanObject,
    mut v_kind_5980_: u8,
    mut v_x_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
    mut v___y_5984_: *mut leanh::LeanObject,
    mut v___y_5985_: *mut leanh::LeanObject,
    mut v___y_5986_: *mut leanh::LeanObject,
    mut v___y_5987_: *mut leanh::LeanObject,
    mut v___y_5988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5990_ = lean_array_push(v_acc_5977_, v_x_5981_);
    v___x_5991_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5978_, v_k_5979_, v_kind_5980_, v___x_5990_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
    return v___x_5991_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10___boxed(
    mut v_declInfos_5992_: *mut leanh::LeanObject,
    mut v_k_5993_: *mut leanh::LeanObject,
    mut v_kind_5994_: *mut leanh::LeanObject,
    mut v_acc_5995_: *mut leanh::LeanObject,
    mut v___y_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
    mut v___y_6000_: *mut leanh::LeanObject,
    mut v___y_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6004_: u8 = 0;
    let mut v_res_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6004_ = (leanh::lean_unbox(v_kind_5994_) as u8);
    v_res_6005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_5992_, v_k_5993_, v_kind_boxed_6004_, v_acc_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
    leanh::lean_dec(v___y_6002_);
    leanh::lean_dec_ref(v___y_6001_);
    leanh::lean_dec(v___y_6000_);
    leanh::lean_dec_ref(v___y_5999_);
    leanh::lean_dec(v___y_5998_);
    leanh::lean_dec_ref(v___y_5997_);
    leanh::lean_dec_ref(v___y_5996_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(
    mut v_declInfos_6008_: *mut leanh::LeanObject,
    mut v_k_6009_: *mut leanh::LeanObject,
    mut v_kind_6010_: u8,
    mut v___y_6011_: *mut leanh::LeanObject,
    mut v___y_6012_: *mut leanh::LeanObject,
    mut v___y_6013_: *mut leanh::LeanObject,
    mut v___y_6014_: *mut leanh::LeanObject,
    mut v___y_6015_: *mut leanh::LeanObject,
    mut v___y_6016_: *mut leanh::LeanObject,
    mut v___y_6017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6019_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___closed__0;
    v___x_6020_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7_spec__10(v_declInfos_6008_, v_k_6009_, v_kind_6010_, v___x_6019_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    return v___x_6020_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7___boxed(
    mut v_declInfos_6021_: *mut leanh::LeanObject,
    mut v_k_6022_: *mut leanh::LeanObject,
    mut v_kind_6023_: *mut leanh::LeanObject,
    mut v___y_6024_: *mut leanh::LeanObject,
    mut v___y_6025_: *mut leanh::LeanObject,
    mut v___y_6026_: *mut leanh::LeanObject,
    mut v___y_6027_: *mut leanh::LeanObject,
    mut v___y_6028_: *mut leanh::LeanObject,
    mut v___y_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6032_: u8 = 0;
    let mut v_res_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6032_ = (leanh::lean_unbox(v_kind_6023_) as u8);
    v_res_6033_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v_declInfos_6021_, v_k_6022_, v_kind_boxed_6032_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_);
    leanh::lean_dec(v___y_6030_);
    leanh::lean_dec_ref(v___y_6029_);
    leanh::lean_dec(v___y_6028_);
    leanh::lean_dec_ref(v___y_6027_);
    leanh::lean_dec(v___y_6026_);
    leanh::lean_dec_ref(v___y_6025_);
    leanh::lean_dec_ref(v___y_6024_);
    return v_res_6033_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(
    mut v_sz_6034_: usize,
    mut v_i_6035_: usize,
    mut v_bs_6036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6037_: u8 = 0;
    let mut v_v_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: u8 = 0;
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6037_ = lean_usize_dec_lt(v_i_6035_, v_sz_6034_);
                if v___x_6037_ == 0 {
                    return v_bs_6036_;
                } else {
                    v_v_6038_ = lean_array_uget(v_bs_6036_, v_i_6035_);
                    v_fst_6039_ = leanh::lean_ctor_get(v_v_6038_, 0);
                    v_snd_6040_ = leanh::lean_ctor_get(v_v_6038_, 1);
                    v_isSharedCheck_6056_ = (!leanh::lean_is_exclusive(v_v_6038_)) as u8;
                    if v_isSharedCheck_6056_ == 0 {
                        v___x_6042_ = v_v_6038_;
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6040_);
                        leanh::lean_inc(v_fst_6039_);
                        leanh::lean_dec(v_v_6038_);
                        v___x_6042_ = leanh::lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6044_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_6045_ = lean_array_uset(v_bs_6036_, v_i_6035_, v___x_6044_);
                v___x_6046_ = 0;
                v___x_6047_ = leanh::lean_box((v___x_6046_) as usize);
                if v_isShared_6043_ == 0 {
                    leanh::lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                    v___x_6049_ = v___x_6042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 1, v_snd_6040_);
                    v___x_6049_ = v_reuseFailAlloc_6055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6050_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6050_, 0, v_fst_6039_);
                leanh::lean_ctor_set(v___x_6050_, 1, v___x_6049_);
                v___x_6051_ = 1usize;
                v___x_6052_ = lean_usize_add(v_i_6035_, v___x_6051_);
                v___x_6053_ = lean_array_uset(v_bs_x27_6045_, v_i_6035_, v___x_6050_);
                v_i_6035_ = v___x_6052_;
                v_bs_6036_ = v___x_6053_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6___boxed(
    mut v_sz_6057_: *mut leanh::LeanObject,
    mut v_i_6058_: *mut leanh::LeanObject,
    mut v_bs_6059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6060_: usize = 0;
    let mut v_i_boxed_6061_: usize = 0;
    let mut v_res_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6060_ = leanh::lean_unbox_usize(v_sz_6057_);
    leanh::lean_dec(v_sz_6057_);
    v_i_boxed_6061_ = leanh::lean_unbox_usize(v_i_6058_);
    leanh::lean_dec(v_i_6058_);
    v_res_6062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_boxed_6060_, v_i_boxed_6061_, v_bs_6059_);
    return v_res_6062_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(
    mut v_declInfos_6063_: *mut leanh::LeanObject,
    mut v_k_6064_: *mut leanh::LeanObject,
    mut v_kind_6065_: u8,
    mut v___y_6066_: *mut leanh::LeanObject,
    mut v___y_6067_: *mut leanh::LeanObject,
    mut v___y_6068_: *mut leanh::LeanObject,
    mut v___y_6069_: *mut leanh::LeanObject,
    mut v___y_6070_: *mut leanh::LeanObject,
    mut v___y_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_6074_: usize = 0;
    let mut v___x_6075_: usize = 0;
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_6074_ = lean_array_size(v_declInfos_6063_);
    v___x_6075_ = 0usize;
    v___x_6076_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__6(v_sz_6074_, v___x_6075_, v_declInfos_6063_);
    v___x_6077_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4_spec__7(v___x_6076_, v_k_6064_, v_kind_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_);
    return v___x_6077_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4___boxed(
    mut v_declInfos_6078_: *mut leanh::LeanObject,
    mut v_k_6079_: *mut leanh::LeanObject,
    mut v_kind_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
    mut v___y_6082_: *mut leanh::LeanObject,
    mut v___y_6083_: *mut leanh::LeanObject,
    mut v___y_6084_: *mut leanh::LeanObject,
    mut v___y_6085_: *mut leanh::LeanObject,
    mut v___y_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6089_: u8 = 0;
    let mut v_res_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6089_ = (leanh::lean_unbox(v_kind_6080_) as u8);
    v_res_6090_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(
        v_declInfos_6078_,
        v_k_6079_,
        v_kind_boxed_6089_,
        v___y_6081_,
        v___y_6082_,
        v___y_6083_,
        v___y_6084_,
        v___y_6085_,
        v___y_6086_,
        v___y_6087_,
    );
    leanh::lean_dec(v___y_6087_);
    leanh::lean_dec_ref(v___y_6086_);
    leanh::lean_dec(v___y_6085_);
    leanh::lean_dec_ref(v___y_6084_);
    leanh::lean_dec(v___y_6083_);
    leanh::lean_dec_ref(v___y_6082_);
    leanh::lean_dec_ref(v___y_6081_);
    return v_res_6090_;
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor(
    mut v_stx_6119_: *mut leanh::LeanObject,
    mut v_dec_6120_: *mut leanh::LeanObject,
    mut v_a_6121_: *mut leanh::LeanObject,
    mut v_a_6122_: *mut leanh::LeanObject,
    mut v_a_6123_: *mut leanh::LeanObject,
    mut v_a_6124_: *mut leanh::LeanObject,
    mut v_a_6125_: *mut leanh::LeanObject,
    mut v_a_6126_: *mut leanh::LeanObject,
    mut v_a_6127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: u8 = 0;
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: u8 = 0;
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: u8 = 0;
    let mut v___y_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6145_: u8 = 0;
    let mut v___y_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: u8 = 0;
    let mut v___x_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doBlockResultType_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6188_: u8 = 0;
    let mut v___y_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6237_: u8 = 0;
    let mut v___x_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6241_: u8 = 0;
    let mut v___y_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6248_: u8 = 0;
    let mut v___y_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6270_: u8 = 0;
    let mut v___y_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6289_: u8 = 0;
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6305_: u8 = 0;
    let mut v_fst_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6310_: u8 = 0;
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6333_: u8 = 0;
    let mut v___x_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_reuseFailAlloc_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_a_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6346_: u8 = 0;
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6350_: u8 = 0;
    let mut v_a_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6358_: u8 = 0;
    let mut v___y_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6371_: u8 = 0;
    let mut v___y_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6388_: u8 = 0;
    let mut v___y_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_returnsEarly_6394_: u8 = 0;
    let mut v___x_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6398_: usize = 0;
    let mut v___x_6399_: usize = 0;
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6402_: usize = 0;
    let mut v___x_6403_: usize = 0;
    let mut v___x_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: u8 = 0;
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_monadInfo_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutVars_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: u8 = 0;
    let mut v___x_6475_: u8 = 0;
    let mut v___x_6476_: usize = 0;
    let mut v___x_6477_: usize = 0;
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: usize = 0;
    let mut v___x_6480_: usize = 0;
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v_a_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6497_: u8 = 0;
    let mut v_a_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6501_: u8 = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6505_: u8 = 0;
    let mut v_reuseFailAlloc_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_reuseFailAlloc_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut v_a_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6513_: u8 = 0;
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6517_: u8 = 0;
    let mut v_a_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6525_: u8 = 0;
    let mut v_a_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_a_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: u8 = 0;
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_x3f_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6129_ = l_Lean_Elab_Do_expandDoFor___closed__1;
                leanh::lean_inc(v_stx_6119_);
                v___x_6130_ = l_Lean_Syntax_isOfKind(v_stx_6119_, v___x_6129_);
                if v___x_6130_ == 0 {
                    leanh::lean_dec_ref(v_dec_6120_);
                    leanh::lean_dec(v_stx_6119_);
                    v___x_6131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                    return v___x_6131_;
                } else {
                    v___x_6132_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6133_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6132_);
                    leanh::lean_inc(v___x_6133_);
                    v___x_6134_ = l_Lean_Syntax_matchesNull(v___x_6133_, v___x_6132_);
                    if v___x_6134_ == 0 {
                        leanh::lean_dec(v___x_6133_);
                        leanh::lean_dec_ref(v_dec_6120_);
                        leanh::lean_dec(v_stx_6119_);
                        v___x_6135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                        return v___x_6135_;
                    } else {
                        v___x_6136_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6137_ = l_Lean_Syntax_getArg(v___x_6133_, v___x_6136_);
                        leanh::lean_dec(v___x_6133_);
                        v___x_6138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___closed__4;
                        leanh::lean_inc(v___x_6137_);
                        v___x_6139_ = l_Lean_Syntax_isOfKind(v___x_6137_, v___x_6138_);
                        if v___x_6139_ == 0 {
                            leanh::lean_dec(v___x_6137_);
                            leanh::lean_dec_ref(v_dec_6120_);
                            leanh::lean_dec(v_stx_6119_);
                            v___x_6407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                            return v___x_6407_;
                        } else {
                            v_tk_6408_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6136_);
                            v___x_6542_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6136_);
                            v___x_6543_ = l_Lean_Syntax_isNone(v___x_6542_);
                            if v___x_6543_ == 0 {
                                v___x_6544_ = leanh::lean_unsigned_to_nat(2);
                                leanh::lean_inc(v___x_6542_);
                                v___x_6545_ = l_Lean_Syntax_matchesNull(v___x_6542_, v___x_6544_);
                                if v___x_6545_ == 0 {
                                    leanh::lean_dec(v___x_6542_);
                                    leanh::lean_dec(v_tk_6408_);
                                    leanh::lean_dec(v___x_6137_);
                                    leanh::lean_dec_ref(v_dec_6120_);
                                    leanh::lean_dec(v_stx_6119_);
                                    v___x_6546_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                                    return v___x_6546_;
                                } else {
                                    v_h_x3f_6547_ = l_Lean_Syntax_getArg(v___x_6542_, v___x_6136_);
                                    leanh::lean_dec(v___x_6542_);
                                    v___x_6548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6548_, 0, v_h_x3f_6547_);
                                    v_h_x3f_6410_ = v___x_6548_;
                                    v___y_6411_ = v_a_6121_;
                                    v___y_6412_ = v_a_6122_;
                                    v___y_6413_ = v_a_6123_;
                                    v___y_6414_ = v_a_6124_;
                                    v___y_6415_ = v_a_6125_;
                                    v___y_6416_ = v_a_6126_;
                                    v___y_6417_ = v_a_6127_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v___x_6542_);
                                v___x_6549_ = leanh::lean_box(0);
                                v_h_x3f_6410_ = v___x_6549_;
                                v___y_6411_ = v_a_6121_;
                                v___y_6412_ = v_a_6122_;
                                v___y_6413_ = v_a_6123_;
                                v___y_6414_ = v_a_6124_;
                                v___y_6415_ = v_a_6125_;
                                v___y_6416_ = v_a_6126_;
                                v___y_6417_ = v_a_6127_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6167_ = l_Lean_instInhabitedExpr;
                v___x_6168_ = leanh::lean_box((v___x_6139_) as usize);
                leanh::lean_inc(v___y_6142_);
                leanh::lean_inc(v___y_6154_);
                leanh::lean_inc(v___y_6152_);
                leanh::lean_inc_ref(v___y_6144_);
                leanh::lean_inc_ref(v___y_6150_);
                v___f_6169_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__9___boxed as *mut core::ffi::c_void,
                    24,
                    15,
                );
                leanh::lean_closure_set(v___f_6169_, 0, v___x_6167_);
                leanh::lean_closure_set(v___f_6169_, 1, v___x_6136_);
                leanh::lean_closure_set(v___f_6169_, 2, v___y_6156_);
                leanh::lean_closure_set(v___f_6169_, 3, v___y_6150_);
                leanh::lean_closure_set(v___f_6169_, 4, v___y_6144_);
                leanh::lean_closure_set(v___f_6169_, 5, v___y_6152_);
                leanh::lean_closure_set(v___f_6169_, 6, v___y_6146_);
                leanh::lean_closure_set(v___f_6169_, 7, v___y_6153_);
                leanh::lean_closure_set(v___f_6169_, 8, v___y_6147_);
                leanh::lean_closure_set(v___f_6169_, 9, v___y_6148_);
                leanh::lean_closure_set(v___f_6169_, 10, v___x_6168_);
                leanh::lean_closure_set(v___f_6169_, 11, v___y_6154_);
                leanh::lean_closure_set(v___f_6169_, 12, v___y_6142_);
                leanh::lean_closure_set(v___f_6169_, 13, v___y_6141_);
                leanh::lean_closure_set(v___f_6169_, 14, v___x_6132_);
                v___x_6170_ = 0;
                v___x_6171_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_Do_elabDoFor_spec__4(
                    v___y_6166_,
                    v___f_6169_,
                    v___x_6170_,
                    v___y_6159_,
                    v___y_6158_,
                    v___y_6163_,
                    v___y_6161_,
                    v___y_6160_,
                    v___y_6162_,
                    v___y_6157_,
                );
                if leanh::lean_obj_tag(v___x_6171_) == 0 {
                    v_a_6172_ = leanh::lean_ctor_get(v___x_6171_, 0);
                    leanh::lean_inc(v_a_6172_);
                    leanh::lean_dec_ref_known(v___x_6171_, 1);
                    v_doBlockResultType_6173_ = leanh::lean_ctor_get(v___y_6159_, 3);
                    v___x_6174_ = leanh::lean_box((v___y_6145_) as usize);
                    leanh::lean_inc(v___y_6155_);
                    leanh::lean_inc_ref(v_doBlockResultType_6173_);
                    v___y_6175_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__10___boxed as *mut core::ffi::c_void,
                        19,
                        11,
                    );
                    leanh::lean_closure_set(v___y_6175_, 0, v___x_6174_);
                    leanh::lean_closure_set(v___y_6175_, 1, v___y_6144_);
                    leanh::lean_closure_set(v___y_6175_, 2, v___y_6149_);
                    leanh::lean_closure_set(v___y_6175_, 3, v_doBlockResultType_6173_);
                    leanh::lean_closure_set(v___y_6175_, 4, v___y_6150_);
                    leanh::lean_closure_set(v___y_6175_, 5, v___y_6155_);
                    leanh::lean_closure_set(v___y_6175_, 6, v___y_6152_);
                    leanh::lean_closure_set(v___y_6175_, 7, v___y_6143_);
                    leanh::lean_closure_set(v___y_6175_, 8, v___y_6151_);
                    leanh::lean_closure_set(v___y_6175_, 9, v___x_6136_);
                    leanh::lean_closure_set(v___y_6175_, 10, v___x_6132_);
                    v___x_6176_ = leanh::lean_box((v___x_6139_) as usize);
                    v___f_6177_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Do_elabDoFor___lam__11___boxed as *mut core::ffi::c_void,
                        13,
                        4,
                    );
                    leanh::lean_closure_set(v___f_6177_, 0, v___y_6154_);
                    leanh::lean_closure_set(v___f_6177_, 1, v___y_6175_);
                    leanh::lean_closure_set(v___f_6177_, 2, v___x_6132_);
                    leanh::lean_closure_set(v___f_6177_, 3, v___x_6176_);
                    leanh::lean_inc_ref(v___y_6165_);
                    v___x_6178_ =
                        l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
                            v___y_6142_,
                            v___y_6165_,
                            v___f_6177_,
                            v___y_6159_,
                            v___y_6158_,
                            v___y_6163_,
                            v___y_6161_,
                            v___y_6160_,
                            v___y_6162_,
                            v___y_6157_,
                        );
                    if leanh::lean_obj_tag(v___x_6178_) == 0 {
                        v_a_6179_ = leanh::lean_ctor_get(v___x_6178_, 0);
                        leanh::lean_inc(v_a_6179_);
                        leanh::lean_dec_ref_known(v___x_6178_, 1);
                        v___x_6180_ = l_Lean_Expr_app___override(v___y_6164_, v_a_6172_);
                        leanh::lean_inc_ref(v_doBlockResultType_6173_);
                        v___x_6181_ = l_Lean_Elab_Do_mkBindApp(
                            v___y_6165_,
                            v_doBlockResultType_6173_,
                            v___x_6180_,
                            v_a_6179_,
                            v___y_6159_,
                            v___y_6158_,
                            v___y_6163_,
                            v___y_6161_,
                            v___y_6160_,
                            v___y_6162_,
                            v___y_6157_,
                        );
                        return v___x_6181_;
                    } else {
                        leanh::lean_dec(v_a_6172_);
                        leanh::lean_dec_ref(v___y_6165_);
                        leanh::lean_dec_ref(v___y_6164_);
                        return v___x_6178_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6165_);
                    leanh::lean_dec_ref(v___y_6164_);
                    leanh::lean_dec(v___y_6154_);
                    leanh::lean_dec(v___y_6152_);
                    leanh::lean_dec_ref(v___y_6151_);
                    leanh::lean_dec_ref(v___y_6150_);
                    leanh::lean_dec(v___y_6149_);
                    leanh::lean_dec_ref(v___y_6144_);
                    leanh::lean_dec_ref(v___y_6143_);
                    leanh::lean_dec(v___y_6142_);
                    return v___x_6171_;
                }
            }
            2 => {
                v___x_6216_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Do_expandDoFor_spec__0___redArg___lam__1___closed__17;
                v___x_6217_ = l_Lean_Core_mkFreshUserName(v___x_6216_, v___y_6214_, v___y_6215_);
                if leanh::lean_obj_tag(v___x_6217_) == 0 {
                    if leanh::lean_obj_tag(v___y_6204_) == 1 {
                        if leanh::lean_obj_tag(v_snd_6208_) == 1 {
                            leanh::lean_dec_ref(v___y_6203_);
                            v_a_6218_ = leanh::lean_ctor_get(v___x_6217_, 0);
                            leanh::lean_inc(v_a_6218_);
                            leanh::lean_dec_ref_known(v___x_6217_, 1);
                            v_val_6219_ = leanh::lean_ctor_get(v___y_6204_, 0);
                            leanh::lean_inc(v_val_6219_);
                            leanh::lean_dec_ref_known(v___y_6204_, 1);
                            v_val_6220_ = leanh::lean_ctor_get(v_snd_6208_, 0);
                            leanh::lean_inc(v_val_6220_);
                            leanh::lean_dec_ref_known(v_snd_6208_, 1);
                            v___f_6221_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Do_elabDoFor___lam__12___boxed
                                    as *mut core::ffi::c_void,
                                16,
                                7,
                            );
                            leanh::lean_closure_set(v___f_6221_, 0, v___y_6197_);
                            leanh::lean_closure_set(v___f_6221_, 1, v___y_6192_);
                            leanh::lean_closure_set(v___f_6221_, 2, v___x_6136_);
                            leanh::lean_closure_set(v___f_6221_, 3, v___y_6183_);
                            leanh::lean_closure_set(v___f_6221_, 4, v___y_6200_);
                            leanh::lean_closure_set(v___f_6221_, 5, v_val_6220_);
                            leanh::lean_closure_set(v___f_6221_, 6, v___y_6187_);
                            v___x_6222_ = l_Lean_TSyntax_getId(v___y_6206_);
                            leanh::lean_dec(v___y_6206_);
                            v___x_6223_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6223_, 0, v___x_6222_);
                            leanh::lean_ctor_set(v___x_6223_, 1, v___y_6205_);
                            v___x_6224_ = l_Lean_TSyntax_getId(v_val_6219_);
                            leanh::lean_dec(v_val_6219_);
                            v___x_6225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6225_, 0, v___x_6224_);
                            leanh::lean_ctor_set(v___x_6225_, 1, v___f_6221_);
                            v___x_6226_ = leanh::lean_unsigned_to_nat(2);
                            v___x_6227_ = lean_mk_empty_array_with_capacity(v___x_6226_);
                            v___x_6228_ = lean_array_push(v___x_6227_, v___x_6223_);
                            v___x_6229_ = lean_array_push(v___x_6228_, v___x_6225_);
                            leanh::lean_inc_ref(v___y_6189_);
                            v___y_6141_ = v___y_6184_;
                            v___y_6142_ = v_a_6218_;
                            v___y_6143_ = v___y_6185_;
                            v___y_6144_ = v___y_6186_;
                            v___y_6145_ = v___y_6188_;
                            v___y_6146_ = v___y_6189_;
                            v___y_6147_ = v___y_6190_;
                            v___y_6148_ = v___y_6191_;
                            v___y_6149_ = v___y_6193_;
                            v___y_6150_ = v___y_6194_;
                            v___y_6151_ = v___y_6195_;
                            v___y_6152_ = v___y_6196_;
                            v___y_6153_ = v___y_6198_;
                            v___y_6154_ = v___y_6199_;
                            v___y_6155_ = v___y_6201_;
                            v___y_6156_ = v___y_6202_;
                            v___y_6157_ = v___y_6215_;
                            v___y_6158_ = v___y_6210_;
                            v___y_6159_ = v___y_6209_;
                            v___y_6160_ = v___y_6213_;
                            v___y_6161_ = v___y_6212_;
                            v___y_6162_ = v___y_6214_;
                            v___y_6163_ = v___y_6211_;
                            v___y_6164_ = v_fst_6207_;
                            v___y_6165_ = v___y_6189_;
                            v___y_6166_ = v___x_6229_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___y_6206_);
                            leanh::lean_dec_ref(v___y_6205_);
                            leanh::lean_dec_ref(v___y_6200_);
                            leanh::lean_dec(v___y_6197_);
                            leanh::lean_dec(v___y_6192_);
                            leanh::lean_dec_ref(v___y_6187_);
                            leanh::lean_dec_ref(v___y_6183_);
                            v_a_6230_ = leanh::lean_ctor_get(v___x_6217_, 0);
                            leanh::lean_inc(v_a_6230_);
                            leanh::lean_dec_ref_known(v___x_6217_, 1);
                            v___x_6231_ =
                                leanh::lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                            leanh::lean_inc_ref(v___y_6189_);
                            v___y_6141_ = v___y_6184_;
                            v___y_6142_ = v_a_6230_;
                            v___y_6143_ = v___y_6185_;
                            v___y_6144_ = v___y_6186_;
                            v___y_6145_ = v___y_6188_;
                            v___y_6146_ = v___y_6189_;
                            v___y_6147_ = v___y_6190_;
                            v___y_6148_ = v___y_6191_;
                            v___y_6149_ = v___y_6193_;
                            v___y_6150_ = v___y_6194_;
                            v___y_6151_ = v___y_6195_;
                            v___y_6152_ = v___y_6196_;
                            v___y_6153_ = v___y_6198_;
                            v___y_6154_ = v___y_6199_;
                            v___y_6155_ = v___y_6201_;
                            v___y_6156_ = v___y_6202_;
                            v___y_6157_ = v___y_6215_;
                            v___y_6158_ = v___y_6210_;
                            v___y_6159_ = v___y_6209_;
                            v___y_6160_ = v___y_6213_;
                            v___y_6161_ = v___y_6212_;
                            v___y_6162_ = v___y_6214_;
                            v___y_6163_ = v___y_6211_;
                            v___y_6164_ = v_fst_6207_;
                            v___y_6165_ = v___y_6189_;
                            v___y_6166_ = v___x_6231_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___y_6206_);
                        leanh::lean_dec_ref(v___y_6205_);
                        leanh::lean_dec_ref(v___y_6200_);
                        leanh::lean_dec(v___y_6197_);
                        leanh::lean_dec(v___y_6192_);
                        leanh::lean_dec_ref(v___y_6187_);
                        leanh::lean_dec_ref(v___y_6183_);
                        v_a_6232_ = leanh::lean_ctor_get(v___x_6217_, 0);
                        leanh::lean_inc(v_a_6232_);
                        leanh::lean_dec_ref_known(v___x_6217_, 1);
                        v___x_6233_ =
                            leanh::lean_apply_2(v___y_6203_, v___y_6204_, v_snd_6208_);
                        leanh::lean_inc_ref(v___y_6189_);
                        v___y_6141_ = v___y_6184_;
                        v___y_6142_ = v_a_6232_;
                        v___y_6143_ = v___y_6185_;
                        v___y_6144_ = v___y_6186_;
                        v___y_6145_ = v___y_6188_;
                        v___y_6146_ = v___y_6189_;
                        v___y_6147_ = v___y_6190_;
                        v___y_6148_ = v___y_6191_;
                        v___y_6149_ = v___y_6193_;
                        v___y_6150_ = v___y_6194_;
                        v___y_6151_ = v___y_6195_;
                        v___y_6152_ = v___y_6196_;
                        v___y_6153_ = v___y_6198_;
                        v___y_6154_ = v___y_6199_;
                        v___y_6155_ = v___y_6201_;
                        v___y_6156_ = v___y_6202_;
                        v___y_6157_ = v___y_6215_;
                        v___y_6158_ = v___y_6210_;
                        v___y_6159_ = v___y_6209_;
                        v___y_6160_ = v___y_6213_;
                        v___y_6161_ = v___y_6212_;
                        v___y_6162_ = v___y_6214_;
                        v___y_6163_ = v___y_6211_;
                        v___y_6164_ = v_fst_6207_;
                        v___y_6165_ = v___y_6189_;
                        v___y_6166_ = v___x_6233_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_6208_);
                    leanh::lean_dec_ref(v_fst_6207_);
                    leanh::lean_dec(v___y_6206_);
                    leanh::lean_dec_ref(v___y_6205_);
                    leanh::lean_dec(v___y_6204_);
                    leanh::lean_dec_ref(v___y_6203_);
                    leanh::lean_dec(v___y_6202_);
                    leanh::lean_dec_ref(v___y_6200_);
                    leanh::lean_dec(v___y_6199_);
                    leanh::lean_dec_ref(v___y_6198_);
                    leanh::lean_dec(v___y_6197_);
                    leanh::lean_dec(v___y_6196_);
                    leanh::lean_dec_ref(v___y_6195_);
                    leanh::lean_dec_ref(v___y_6194_);
                    leanh::lean_dec(v___y_6193_);
                    leanh::lean_dec(v___y_6192_);
                    leanh::lean_dec(v___y_6191_);
                    leanh::lean_dec(v___y_6190_);
                    leanh::lean_dec_ref(v___y_6189_);
                    leanh::lean_dec_ref(v___y_6187_);
                    leanh::lean_dec_ref(v___y_6186_);
                    leanh::lean_dec_ref(v___y_6185_);
                    leanh::lean_dec(v___y_6184_);
                    leanh::lean_dec_ref(v___y_6183_);
                    v_a_6234_ = leanh::lean_ctor_get(v___x_6217_, 0);
                    v_isSharedCheck_6241_ = (!leanh::lean_is_exclusive(v___x_6217_)) as u8;
                    if v_isSharedCheck_6241_ == 0 {
                        v___x_6236_ = v___x_6217_;
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6234_);
                        leanh::lean_dec(v___x_6217_);
                        v___x_6236_ = leanh::lean_box(0);
                        v_isShared_6237_ = v_isSharedCheck_6241_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6237_ == 0 {
                    v___x_6239_ = v___x_6236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6240_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
                    v___x_6239_ = v_reuseFailAlloc_6240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6239_;
            }
            5 => {
                v___x_6277_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___y_6255_);
                leanh::lean_inc(v___y_6259_);
                leanh::lean_inc_ref(v___y_6263_);
                leanh::lean_inc(v___y_6261_);
                leanh::lean_inc_ref(v___y_6273_);
                leanh::lean_inc(v___y_6266_);
                leanh::lean_inc_ref(v___y_6260_);
                v___x_6278_ = leanh::lean_apply_8(
                    v___y_6255_,
                    v___x_6277_,
                    v___y_6260_,
                    v___y_6266_,
                    v___y_6273_,
                    v___y_6261_,
                    v___y_6263_,
                    v___y_6259_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6278_) == 0 {
                    v_a_6279_ = leanh::lean_ctor_get(v___x_6278_, 0);
                    leanh::lean_inc(v_a_6279_);
                    leanh::lean_dec_ref_known(v___x_6278_, 1);
                    v_m_6280_ = leanh::lean_ctor_get(v___y_6274_, 0);
                    v_u_6281_ = leanh::lean_ctor_get(v___y_6274_, 1);
                    v_v_6282_ = leanh::lean_ctor_get(v___y_6274_, 2);
                    leanh::lean_inc(v_u_6281_);
                    v___x_6283_ = l_Lean_Meta_mkProdMkN(
                        v_a_6279_,
                        v_u_6281_,
                        v___y_6273_,
                        v___y_6261_,
                        v___y_6263_,
                        v___y_6259_,
                    );
                    if leanh::lean_obj_tag(v___x_6283_) == 0 {
                        v_a_6284_ = leanh::lean_ctor_get(v___x_6283_, 0);
                        leanh::lean_inc(v_a_6284_);
                        leanh::lean_dec_ref_known(v___x_6283_, 1);
                        if leanh::lean_obj_tag(v___y_6262_) == 0 {
                            v_fst_6285_ = leanh::lean_ctor_get(v_a_6284_, 0);
                            v_snd_6286_ = leanh::lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6305_ =
                                (!leanh::lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6305_ == 0 {
                                v___x_6288_ = v_a_6284_;
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_6286_);
                                leanh::lean_inc(v_fst_6285_);
                                leanh::lean_dec(v_a_6284_);
                                v___x_6288_ = leanh::lean_box(0);
                                v_isShared_6289_ = v_isSharedCheck_6305_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_fst_6306_ = leanh::lean_ctor_get(v_a_6284_, 0);
                            v_snd_6307_ = leanh::lean_ctor_get(v_a_6284_, 1);
                            v_isSharedCheck_6342_ =
                                (!leanh::lean_is_exclusive(v_a_6284_)) as u8;
                            if v_isSharedCheck_6342_ == 0 {
                                v___x_6309_ = v_a_6284_;
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_6307_);
                                leanh::lean_inc(v_fst_6306_);
                                leanh::lean_dec(v_a_6284_);
                                v___x_6309_ = leanh::lean_box(0);
                                v_isShared_6310_ = v_isSharedCheck_6342_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___y_6276_);
                        leanh::lean_dec(v___y_6275_);
                        leanh::lean_dec_ref(v___y_6272_);
                        leanh::lean_dec_ref(v___y_6269_);
                        leanh::lean_dec(v___y_6268_);
                        leanh::lean_dec(v___y_6267_);
                        leanh::lean_dec_ref(v___y_6265_);
                        leanh::lean_dec_ref(v___y_6264_);
                        leanh::lean_dec(v___y_6262_);
                        leanh::lean_dec_ref(v___y_6258_);
                        leanh::lean_dec(v___y_6257_);
                        leanh::lean_dec_ref(v___y_6256_);
                        leanh::lean_dec_ref(v___y_6255_);
                        leanh::lean_dec(v___y_6254_);
                        leanh::lean_dec_ref(v___y_6253_);
                        leanh::lean_dec_ref(v___y_6252_);
                        leanh::lean_dec(v___y_6251_);
                        leanh::lean_dec(v___y_6250_);
                        leanh::lean_dec(v___y_6249_);
                        leanh::lean_dec_ref(v___y_6247_);
                        leanh::lean_dec_ref(v___y_6246_);
                        leanh::lean_dec_ref(v___y_6245_);
                        leanh::lean_dec(v___y_6244_);
                        leanh::lean_dec_ref(v___y_6243_);
                        v_a_6343_ = leanh::lean_ctor_get(v___x_6283_, 0);
                        v_isSharedCheck_6350_ =
                            (!leanh::lean_is_exclusive(v___x_6283_)) as u8;
                        if v_isSharedCheck_6350_ == 0 {
                            v___x_6345_ = v___x_6283_;
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6343_);
                            leanh::lean_dec(v___x_6283_);
                            v___x_6345_ = leanh::lean_box(0);
                            v_isShared_6346_ = v_isSharedCheck_6350_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_6276_);
                    leanh::lean_dec(v___y_6275_);
                    leanh::lean_dec_ref(v___y_6272_);
                    leanh::lean_dec_ref(v___y_6269_);
                    leanh::lean_dec(v___y_6268_);
                    leanh::lean_dec(v___y_6267_);
                    leanh::lean_dec_ref(v___y_6265_);
                    leanh::lean_dec_ref(v___y_6264_);
                    leanh::lean_dec(v___y_6262_);
                    leanh::lean_dec_ref(v___y_6258_);
                    leanh::lean_dec(v___y_6257_);
                    leanh::lean_dec_ref(v___y_6256_);
                    leanh::lean_dec_ref(v___y_6255_);
                    leanh::lean_dec(v___y_6254_);
                    leanh::lean_dec_ref(v___y_6253_);
                    leanh::lean_dec_ref(v___y_6252_);
                    leanh::lean_dec(v___y_6251_);
                    leanh::lean_dec(v___y_6250_);
                    leanh::lean_dec(v___y_6249_);
                    leanh::lean_dec_ref(v___y_6247_);
                    leanh::lean_dec_ref(v___y_6246_);
                    leanh::lean_dec_ref(v___y_6245_);
                    leanh::lean_dec(v___y_6244_);
                    leanh::lean_dec_ref(v___y_6243_);
                    v_a_6351_ = leanh::lean_ctor_get(v___x_6278_, 0);
                    v_isSharedCheck_6358_ = (!leanh::lean_is_exclusive(v___x_6278_)) as u8;
                    if v_isSharedCheck_6358_ == 0 {
                        v___x_6353_ = v___x_6278_;
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6351_);
                        leanh::lean_dec(v___x_6278_);
                        v___x_6353_ = leanh::lean_box(0);
                        v_isShared_6354_ = v_isSharedCheck_6358_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6290_ = l_Lean_Elab_Do_elabDoFor___closed__1;
                v___x_6291_ = leanh::lean_box(0);
                leanh::lean_inc(v_v_6282_);
                if v_isShared_6289_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6288_, 1);
                    leanh::lean_ctor_set(v___x_6288_, 1, v___x_6291_);
                    leanh::lean_ctor_set(v___x_6288_, 0, v_v_6282_);
                    v___x_6293_ = v___x_6288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6304_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6304_, 0, v_v_6282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6304_, 1, v___x_6291_);
                    v___x_6293_ = v_reuseFailAlloc_6304_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v_u_6281_);
                v___x_6294_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6294_, 0, v_u_6281_);
                leanh::lean_ctor_set(v___x_6294_, 1, v___x_6293_);
                v___x_6295_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6295_, 0, v___y_6267_);
                leanh::lean_ctor_set(v___x_6295_, 1, v___x_6294_);
                v___x_6296_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6296_, 0, v___y_6268_);
                leanh::lean_ctor_set(v___x_6296_, 1, v___x_6295_);
                leanh::lean_inc_ref(v___x_6296_);
                v___x_6297_ = l_Lean_mkConst(v___x_6290_, v___x_6296_);
                leanh::lean_inc_ref(v___y_6258_);
                leanh::lean_inc_ref(v___y_6272_);
                leanh::lean_inc_ref(v_m_6280_);
                v___x_6298_ = l_Lean_mkApp3(v___x_6297_, v_m_6280_, v___y_6272_, v___y_6258_);
                v___x_6299_ = l_Lean_Elab_Term_mkInstMVar(
                    v___x_6298_,
                    v___x_6277_,
                    v___y_6260_,
                    v___y_6266_,
                    v___y_6273_,
                    v___y_6261_,
                    v___y_6263_,
                    v___y_6259_,
                );
                if leanh::lean_obj_tag(v___x_6299_) == 0 {
                    v_a_6300_ = leanh::lean_ctor_get(v___x_6299_, 0);
                    leanh::lean_inc(v_a_6300_);
                    leanh::lean_dec_ref_known(v___x_6299_, 1);
                    v___x_6301_ = l_Lean_Elab_Do_elabDoFor___closed__3;
                    v___x_6302_ = l_Lean_mkConst(v___x_6301_, v___x_6296_);
                    leanh::lean_inc(v_snd_6286_);
                    leanh::lean_inc_ref(v_m_6280_);
                    v___x_6303_ = l_Lean_mkApp7(
                        v___x_6302_,
                        v_m_6280_,
                        v___y_6272_,
                        v___y_6258_,
                        v_a_6300_,
                        v_snd_6286_,
                        v___y_6264_,
                        v_fst_6285_,
                    );
                    leanh::lean_inc(v_u_6281_);
                    v___y_6183_ = v___y_6243_;
                    v___y_6184_ = v___y_6244_;
                    v___y_6185_ = v___y_6245_;
                    v___y_6186_ = v___y_6246_;
                    v___y_6187_ = v___y_6247_;
                    v___y_6188_ = v___y_6248_;
                    v___y_6189_ = v_snd_6286_;
                    v___y_6190_ = v___x_6277_;
                    v___y_6191_ = v___y_6249_;
                    v___y_6192_ = v___y_6250_;
                    v___y_6193_ = v___y_6251_;
                    v___y_6194_ = v___y_6252_;
                    v___y_6195_ = v___y_6253_;
                    v___y_6196_ = v_u_6281_;
                    v___y_6197_ = v___y_6254_;
                    v___y_6198_ = v___y_6255_;
                    v___y_6199_ = v___y_6276_;
                    v___y_6200_ = v___y_6256_;
                    v___y_6201_ = v_v_6282_;
                    v___y_6202_ = v___y_6257_;
                    v___y_6203_ = v___y_6269_;
                    v___y_6204_ = v___y_6262_;
                    v___y_6205_ = v___y_6265_;
                    v___y_6206_ = v___y_6275_;
                    v_fst_6207_ = v___x_6303_;
                    v_snd_6208_ = v___x_6277_;
                    v___y_6209_ = v___y_6271_;
                    v___y_6210_ = v___y_6260_;
                    v___y_6211_ = v___y_6266_;
                    v___y_6212_ = v___y_6273_;
                    v___y_6213_ = v___y_6261_;
                    v___y_6214_ = v___y_6263_;
                    v___y_6215_ = v___y_6259_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_6296_, 2);
                    leanh::lean_dec(v_snd_6286_);
                    leanh::lean_dec(v_fst_6285_);
                    leanh::lean_dec(v___y_6276_);
                    leanh::lean_dec(v___y_6275_);
                    leanh::lean_dec_ref(v___y_6272_);
                    leanh::lean_dec_ref(v___y_6269_);
                    leanh::lean_dec_ref(v___y_6265_);
                    leanh::lean_dec_ref(v___y_6264_);
                    leanh::lean_dec_ref(v___y_6258_);
                    leanh::lean_dec(v___y_6257_);
                    leanh::lean_dec_ref(v___y_6256_);
                    leanh::lean_dec_ref(v___y_6255_);
                    leanh::lean_dec(v___y_6254_);
                    leanh::lean_dec_ref(v___y_6253_);
                    leanh::lean_dec_ref(v___y_6252_);
                    leanh::lean_dec(v___y_6251_);
                    leanh::lean_dec(v___y_6250_);
                    leanh::lean_dec(v___y_6249_);
                    leanh::lean_dec_ref(v___y_6247_);
                    leanh::lean_dec_ref(v___y_6246_);
                    leanh::lean_dec_ref(v___y_6245_);
                    leanh::lean_dec(v___y_6244_);
                    leanh::lean_dec_ref(v___y_6243_);
                    return v___x_6299_;
                }
            }
            8 => {
                v___x_6311_ = l_Lean_Elab_Do_elabDoFor___closed__4;
                v___x_6312_ = leanh::lean_box(0);
                leanh::lean_inc(v___y_6268_);
                if v_isShared_6310_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6309_, 1);
                    leanh::lean_ctor_set(v___x_6309_, 1, v___x_6312_);
                    leanh::lean_ctor_set(v___x_6309_, 0, v___y_6268_);
                    v___x_6314_ = v___x_6309_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 0, v___y_6268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 1, v___x_6312_);
                    v___x_6314_ = v_reuseFailAlloc_6341_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc(v___y_6267_);
                v___x_6315_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6315_, 0, v___y_6267_);
                leanh::lean_ctor_set(v___x_6315_, 1, v___x_6314_);
                v___x_6316_ = l_Lean_mkConst(v___x_6311_, v___x_6315_);
                leanh::lean_inc_ref(v___y_6272_);
                leanh::lean_inc_ref(v___y_6258_);
                v___x_6317_ = l_Lean_mkAppB(v___x_6316_, v___y_6258_, v___y_6272_);
                v___x_6318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6318_, 0, v___x_6317_);
                v___x_6319_ = l_Lean_Elab_Do_elabDoFor___closed__6;
                v___x_6320_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_6318_,
                    v___y_6270_,
                    v___x_6319_,
                    v___y_6273_,
                    v___y_6261_,
                    v___y_6263_,
                    v___y_6259_,
                );
                if leanh::lean_obj_tag(v___x_6320_) == 0 {
                    v_a_6321_ = leanh::lean_ctor_get(v___x_6320_, 0);
                    leanh::lean_inc_n(v_a_6321_, 2);
                    leanh::lean_dec_ref_known(v___x_6320_, 1);
                    v___x_6322_ = l_Lean_Elab_Do_elabDoFor___closed__8;
                    leanh::lean_inc(v_v_6282_);
                    v___x_6323_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6323_, 0, v_v_6282_);
                    leanh::lean_ctor_set(v___x_6323_, 1, v___x_6312_);
                    leanh::lean_inc(v_u_6281_);
                    v___x_6324_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6324_, 0, v_u_6281_);
                    leanh::lean_ctor_set(v___x_6324_, 1, v___x_6323_);
                    v___x_6325_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6325_, 0, v___y_6267_);
                    leanh::lean_ctor_set(v___x_6325_, 1, v___x_6324_);
                    v___x_6326_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6326_, 0, v___y_6268_);
                    leanh::lean_ctor_set(v___x_6326_, 1, v___x_6325_);
                    leanh::lean_inc_ref(v___x_6326_);
                    v___x_6327_ = l_Lean_mkConst(v___x_6322_, v___x_6326_);
                    leanh::lean_inc_ref(v___y_6258_);
                    leanh::lean_inc_ref(v___y_6272_);
                    leanh::lean_inc_ref(v_m_6280_);
                    v___x_6328_ =
                        l_Lean_mkApp4(v___x_6327_, v_m_6280_, v___y_6272_, v___y_6258_, v_a_6321_);
                    v___x_6329_ = l_Lean_Elab_Term_mkInstMVar(
                        v___x_6328_,
                        v___x_6277_,
                        v___y_6260_,
                        v___y_6266_,
                        v___y_6273_,
                        v___y_6261_,
                        v___y_6263_,
                        v___y_6259_,
                    );
                    if leanh::lean_obj_tag(v___x_6329_) == 0 {
                        v_a_6330_ = leanh::lean_ctor_get(v___x_6329_, 0);
                        v_isSharedCheck_6340_ =
                            (!leanh::lean_is_exclusive(v___x_6329_)) as u8;
                        if v_isSharedCheck_6340_ == 0 {
                            v___x_6332_ = v___x_6329_;
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6330_);
                            leanh::lean_dec(v___x_6329_);
                            v___x_6332_ = leanh::lean_box(0);
                            v_isShared_6333_ = v_isSharedCheck_6340_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_6326_, 2);
                        leanh::lean_dec(v_a_6321_);
                        leanh::lean_dec(v_snd_6307_);
                        leanh::lean_dec_ref_known(v___y_6262_, 1);
                        leanh::lean_dec(v_fst_6306_);
                        leanh::lean_dec(v___y_6276_);
                        leanh::lean_dec(v___y_6275_);
                        leanh::lean_dec_ref(v___y_6272_);
                        leanh::lean_dec_ref(v___y_6269_);
                        leanh::lean_dec_ref(v___y_6265_);
                        leanh::lean_dec_ref(v___y_6264_);
                        leanh::lean_dec_ref(v___y_6258_);
                        leanh::lean_dec(v___y_6257_);
                        leanh::lean_dec_ref(v___y_6256_);
                        leanh::lean_dec_ref(v___y_6255_);
                        leanh::lean_dec(v___y_6254_);
                        leanh::lean_dec_ref(v___y_6253_);
                        leanh::lean_dec_ref(v___y_6252_);
                        leanh::lean_dec(v___y_6251_);
                        leanh::lean_dec(v___y_6250_);
                        leanh::lean_dec(v___y_6249_);
                        leanh::lean_dec_ref(v___y_6247_);
                        leanh::lean_dec_ref(v___y_6246_);
                        leanh::lean_dec_ref(v___y_6245_);
                        leanh::lean_dec(v___y_6244_);
                        leanh::lean_dec_ref(v___y_6243_);
                        return v___x_6329_;
                    }
                } else {
                    leanh::lean_dec(v_snd_6307_);
                    leanh::lean_dec_ref_known(v___y_6262_, 1);
                    leanh::lean_dec(v_fst_6306_);
                    leanh::lean_dec(v___y_6276_);
                    leanh::lean_dec(v___y_6275_);
                    leanh::lean_dec_ref(v___y_6272_);
                    leanh::lean_dec_ref(v___y_6269_);
                    leanh::lean_dec(v___y_6268_);
                    leanh::lean_dec(v___y_6267_);
                    leanh::lean_dec_ref(v___y_6265_);
                    leanh::lean_dec_ref(v___y_6264_);
                    leanh::lean_dec_ref(v___y_6258_);
                    leanh::lean_dec(v___y_6257_);
                    leanh::lean_dec_ref(v___y_6256_);
                    leanh::lean_dec_ref(v___y_6255_);
                    leanh::lean_dec(v___y_6254_);
                    leanh::lean_dec_ref(v___y_6253_);
                    leanh::lean_dec_ref(v___y_6252_);
                    leanh::lean_dec(v___y_6251_);
                    leanh::lean_dec(v___y_6250_);
                    leanh::lean_dec(v___y_6249_);
                    leanh::lean_dec_ref(v___y_6247_);
                    leanh::lean_dec_ref(v___y_6246_);
                    leanh::lean_dec_ref(v___y_6245_);
                    leanh::lean_dec(v___y_6244_);
                    leanh::lean_dec_ref(v___y_6243_);
                    return v___x_6320_;
                }
            }
            10 => {
                v___x_6334_ = l_Lean_Elab_Do_elabDoFor___closed__10;
                v___x_6335_ = l_Lean_mkConst(v___x_6334_, v___x_6326_);
                leanh::lean_inc(v_snd_6307_);
                leanh::lean_inc(v_a_6321_);
                leanh::lean_inc_ref(v_m_6280_);
                v___x_6336_ = l_Lean_mkApp8(
                    v___x_6335_,
                    v_m_6280_,
                    v___y_6272_,
                    v___y_6258_,
                    v_a_6321_,
                    v_a_6330_,
                    v_snd_6307_,
                    v___y_6264_,
                    v_fst_6306_,
                );
                if v_isShared_6333_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6332_, 1);
                    leanh::lean_ctor_set(v___x_6332_, 0, v_a_6321_);
                    v___x_6338_ = v___x_6332_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6321_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc(v_u_6281_);
                v___y_6183_ = v___y_6243_;
                v___y_6184_ = v___y_6244_;
                v___y_6185_ = v___y_6245_;
                v___y_6186_ = v___y_6246_;
                v___y_6187_ = v___y_6247_;
                v___y_6188_ = v___y_6248_;
                v___y_6189_ = v_snd_6307_;
                v___y_6190_ = v___x_6277_;
                v___y_6191_ = v___y_6249_;
                v___y_6192_ = v___y_6250_;
                v___y_6193_ = v___y_6251_;
                v___y_6194_ = v___y_6252_;
                v___y_6195_ = v___y_6253_;
                v___y_6196_ = v_u_6281_;
                v___y_6197_ = v___y_6254_;
                v___y_6198_ = v___y_6255_;
                v___y_6199_ = v___y_6276_;
                v___y_6200_ = v___y_6256_;
                v___y_6201_ = v_v_6282_;
                v___y_6202_ = v___y_6257_;
                v___y_6203_ = v___y_6269_;
                v___y_6204_ = v___y_6262_;
                v___y_6205_ = v___y_6265_;
                v___y_6206_ = v___y_6275_;
                v_fst_6207_ = v___x_6336_;
                v_snd_6208_ = v___x_6338_;
                v___y_6209_ = v___y_6271_;
                v___y_6210_ = v___y_6260_;
                v___y_6211_ = v___y_6266_;
                v___y_6212_ = v___y_6273_;
                v___y_6213_ = v___y_6261_;
                v___y_6214_ = v___y_6263_;
                v___y_6215_ = v___y_6259_;
                state = 2;
                continue;
            }
            12 => {
                if v_isShared_6346_ == 0 {
                    v___x_6348_ = v___x_6345_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6349_, 0, v_a_6343_);
                    v___x_6348_ = v_reuseFailAlloc_6349_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6348_;
            }
            14 => {
                if v_isShared_6354_ == 0 {
                    v___x_6356_ = v___x_6353_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6357_, 0, v_a_6351_);
                    v___x_6356_ = v_reuseFailAlloc_6357_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6356_;
            }
            16 => {
                v_returnsEarly_6394_ = leanh::lean_ctor_get_uint8(
                    v___y_6378_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 2) as u32,
                );
                leanh::lean_dec_ref(v___y_6378_);
                v___x_6395_ = leanh::lean_box((v_returnsEarly_6394_) as usize);
                v___x_6396_ = leanh::lean_box((v___y_6371_) as usize);
                leanh::lean_inc_ref(v___y_6369_);
                leanh::lean_inc_ref(v___y_6375_);
                leanh::lean_inc_ref(v___y_6393_);
                v___f_6397_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Do_elabDoFor___lam__3___boxed as *mut core::ffi::c_void,
                    14,
                    6,
                );
                leanh::lean_closure_set(v___f_6397_, 0, v___y_6393_);
                leanh::lean_closure_set(v___f_6397_, 1, v___y_6375_);
                leanh::lean_closure_set(v___f_6397_, 2, v___x_6395_);
                leanh::lean_closure_set(v___f_6397_, 3, v___x_6136_);
                leanh::lean_closure_set(v___f_6397_, 4, v___y_6369_);
                leanh::lean_closure_set(v___f_6397_, 5, v___x_6396_);
                if v_returnsEarly_6394_ == 0 {
                    leanh::lean_dec(v___y_6385_);
                    v_sz_6398_ = lean_array_size(v___y_6393_);
                    v___x_6399_ = 0usize;
                    leanh::lean_inc_ref(v___y_6393_);
                    v___x_6400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_6398_, v___x_6399_, v___y_6393_);
                    v___x_6401_ = lean_array_to_list(v___x_6400_);
                    v___y_6243_ = v___y_6360_;
                    v___y_6244_ = v___y_6361_;
                    v___y_6245_ = v___y_6362_;
                    v___y_6246_ = v___y_6363_;
                    v___y_6247_ = v___y_6365_;
                    v___y_6248_ = v_returnsEarly_6394_;
                    v___y_6249_ = v___y_6366_;
                    v___y_6250_ = v___y_6367_;
                    v___y_6251_ = v___y_6368_;
                    v___y_6252_ = v___y_6369_;
                    v___y_6253_ = v___y_6393_;
                    v___y_6254_ = v___y_6372_;
                    v___y_6255_ = v___f_6397_;
                    v___y_6256_ = v___y_6373_;
                    v___y_6257_ = v___y_6374_;
                    v___y_6258_ = v___y_6376_;
                    v___y_6259_ = v___y_6377_;
                    v___y_6260_ = v___y_6379_;
                    v___y_6261_ = v___y_6380_;
                    v___y_6262_ = v___y_6381_;
                    v___y_6263_ = v___y_6382_;
                    v___y_6264_ = v___y_6383_;
                    v___y_6265_ = v___y_6364_;
                    v___y_6266_ = v___y_6384_;
                    v___y_6267_ = v___y_6386_;
                    v___y_6268_ = v___y_6387_;
                    v___y_6269_ = v___y_6370_;
                    v___y_6270_ = v___y_6388_;
                    v___y_6271_ = v___y_6389_;
                    v___y_6272_ = v___y_6391_;
                    v___y_6273_ = v___y_6390_;
                    v___y_6274_ = v___y_6375_;
                    v___y_6275_ = v___y_6392_;
                    v___y_6276_ = v___x_6401_;
                    state = 5;
                    continue;
                } else {
                    v_sz_6402_ = lean_array_size(v___y_6393_);
                    v___x_6403_ = 0usize;
                    leanh::lean_inc_ref(v___y_6393_);
                    v___x_6404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_elabDoFor_spec__6(v_sz_6402_, v___x_6403_, v___y_6393_);
                    v___x_6405_ = lean_array_to_list(v___x_6404_);
                    v___x_6406_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6406_, 0, v___y_6385_);
                    leanh::lean_ctor_set(v___x_6406_, 1, v___x_6405_);
                    v___y_6243_ = v___y_6360_;
                    v___y_6244_ = v___y_6361_;
                    v___y_6245_ = v___y_6362_;
                    v___y_6246_ = v___y_6363_;
                    v___y_6247_ = v___y_6365_;
                    v___y_6248_ = v_returnsEarly_6394_;
                    v___y_6249_ = v___y_6366_;
                    v___y_6250_ = v___y_6367_;
                    v___y_6251_ = v___y_6368_;
                    v___y_6252_ = v___y_6369_;
                    v___y_6253_ = v___y_6393_;
                    v___y_6254_ = v___y_6372_;
                    v___y_6255_ = v___f_6397_;
                    v___y_6256_ = v___y_6373_;
                    v___y_6257_ = v___y_6374_;
                    v___y_6258_ = v___y_6376_;
                    v___y_6259_ = v___y_6377_;
                    v___y_6260_ = v___y_6379_;
                    v___y_6261_ = v___y_6380_;
                    v___y_6262_ = v___y_6381_;
                    v___y_6263_ = v___y_6382_;
                    v___y_6264_ = v___y_6383_;
                    v___y_6265_ = v___y_6364_;
                    v___y_6266_ = v___y_6384_;
                    v___y_6267_ = v___y_6386_;
                    v___y_6268_ = v___y_6387_;
                    v___y_6269_ = v___y_6370_;
                    v___y_6270_ = v___y_6388_;
                    v___y_6271_ = v___y_6389_;
                    v___y_6272_ = v___y_6391_;
                    v___y_6273_ = v___y_6390_;
                    v___y_6274_ = v___y_6375_;
                    v___y_6275_ = v___y_6392_;
                    v___y_6276_ = v___x_6406_;
                    state = 5;
                    continue;
                }
            }
            17 => {
                v_x_6418_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6132_);
                v___x_6419_ = l_Lean_Elab_Do_expandDoFor___closed__16;
                leanh::lean_inc(v_x_6418_);
                v___x_6420_ = l_Lean_Syntax_isOfKind(v_x_6418_, v___x_6419_);
                if v___x_6420_ == 0 {
                    leanh::lean_dec(v_x_6418_);
                    leanh::lean_dec(v_h_x3f_6410_);
                    leanh::lean_dec(v_tk_6408_);
                    leanh::lean_dec(v___x_6137_);
                    leanh::lean_dec_ref(v_dec_6120_);
                    leanh::lean_dec(v_stx_6119_);
                    v___x_6421_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_elabDoFor_spec__0___redArg();
                    return v___x_6421_;
                } else {
                    v___x_6422_ = l_Lean_Elab_Do_DoElemCont_ensureUnitAt(
                        v_dec_6120_,
                        v_tk_6408_,
                        v___y_6411_,
                        v___y_6412_,
                        v___y_6413_,
                        v___y_6414_,
                        v___y_6415_,
                        v___y_6416_,
                        v___y_6417_,
                    );
                    leanh::lean_dec(v_tk_6408_);
                    if leanh::lean_obj_tag(v___x_6422_) == 0 {
                        v_a_6423_ = leanh::lean_ctor_get(v___x_6422_, 0);
                        leanh::lean_inc(v_a_6423_);
                        leanh::lean_dec_ref_known(v___x_6422_, 1);
                        v___x_6424_ = lean_mk_empty_array_with_capacity(v___x_6132_);
                        leanh::lean_inc(v_x_6418_);
                        v___x_6425_ = lean_array_push(v___x_6424_, v_x_6418_);
                        v___x_6426_ = l_Lean_Elab_Do_checkMutVarsForShadowing(
                            v___x_6425_,
                            v___y_6411_,
                            v___y_6412_,
                            v___y_6413_,
                            v___y_6414_,
                            v___y_6415_,
                            v___y_6416_,
                            v___y_6417_,
                        );
                        leanh::lean_dec_ref(v___x_6425_);
                        if leanh::lean_obj_tag(v___x_6426_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6426_, 1);
                            v___x_6427_ = l_Lean_Meta_mkFreshLevelMVar(
                                v___y_6414_,
                                v___y_6415_,
                                v___y_6416_,
                                v___y_6417_,
                            );
                            if leanh::lean_obj_tag(v___x_6427_) == 0 {
                                v_a_6428_ = leanh::lean_ctor_get(v___x_6427_, 0);
                                leanh::lean_inc(v_a_6428_);
                                leanh::lean_dec_ref_known(v___x_6427_, 1);
                                v___x_6429_ = l_Lean_Meta_mkFreshLevelMVar(
                                    v___y_6414_,
                                    v___y_6415_,
                                    v___y_6416_,
                                    v___y_6417_,
                                );
                                if leanh::lean_obj_tag(v___x_6429_) == 0 {
                                    v_a_6430_ = leanh::lean_ctor_get(v___x_6429_, 0);
                                    leanh::lean_inc(v_a_6430_);
                                    leanh::lean_dec_ref_known(v___x_6429_, 1);
                                    leanh::lean_inc(v_a_6428_);
                                    v___x_6431_ = l_Lean_Level_succ___override(v_a_6428_);
                                    v___x_6432_ = l_Lean_mkSort(v___x_6431_);
                                    v___x_6433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_6433_, 0, v___x_6432_);
                                    v___x_6434_ = 0;
                                    v___x_6435_ = l_Lean_Elab_Do_elabDoFor___closed__12;
                                    v___x_6436_ = l_Lean_Meta_mkFreshExprMVar(
                                        v___x_6433_,
                                        v___x_6434_,
                                        v___x_6435_,
                                        v___y_6414_,
                                        v___y_6415_,
                                        v___y_6416_,
                                        v___y_6417_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6436_) == 0 {
                                        v_a_6437_ = leanh::lean_ctor_get(v___x_6436_, 0);
                                        v_isSharedCheck_6509_ =
                                            (!leanh::lean_is_exclusive(v___x_6436_)) as u8;
                                        if v_isSharedCheck_6509_ == 0 {
                                            v___x_6439_ = v___x_6436_;
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6437_);
                                            leanh::lean_dec(v___x_6436_);
                                            v___x_6439_ = leanh::lean_box(0);
                                            v_isShared_6440_ = v_isSharedCheck_6509_;
                                            state = 18;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6430_);
                                        leanh::lean_dec(v_a_6428_);
                                        leanh::lean_dec(v_a_6423_);
                                        leanh::lean_dec(v_x_6418_);
                                        leanh::lean_dec(v_h_x3f_6410_);
                                        leanh::lean_dec(v___x_6137_);
                                        leanh::lean_dec(v_stx_6119_);
                                        return v___x_6436_;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6428_);
                                    leanh::lean_dec(v_a_6423_);
                                    leanh::lean_dec(v_x_6418_);
                                    leanh::lean_dec(v_h_x3f_6410_);
                                    leanh::lean_dec(v___x_6137_);
                                    leanh::lean_dec(v_stx_6119_);
                                    v_a_6510_ = leanh::lean_ctor_get(v___x_6429_, 0);
                                    v_isSharedCheck_6517_ =
                                        (!leanh::lean_is_exclusive(v___x_6429_)) as u8;
                                    if v_isSharedCheck_6517_ == 0 {
                                        v___x_6512_ = v___x_6429_;
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6510_);
                                        leanh::lean_dec(v___x_6429_);
                                        v___x_6512_ = leanh::lean_box(0);
                                        v_isShared_6513_ = v_isSharedCheck_6517_;
                                        state = 28;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6423_);
                                leanh::lean_dec(v_x_6418_);
                                leanh::lean_dec(v_h_x3f_6410_);
                                leanh::lean_dec(v___x_6137_);
                                leanh::lean_dec(v_stx_6119_);
                                v_a_6518_ = leanh::lean_ctor_get(v___x_6427_, 0);
                                v_isSharedCheck_6525_ =
                                    (!leanh::lean_is_exclusive(v___x_6427_)) as u8;
                                if v_isSharedCheck_6525_ == 0 {
                                    v___x_6520_ = v___x_6427_;
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6518_);
                                    leanh::lean_dec(v___x_6427_);
                                    v___x_6520_ = leanh::lean_box(0);
                                    v_isShared_6521_ = v_isSharedCheck_6525_;
                                    state = 30;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_6423_);
                            leanh::lean_dec(v_x_6418_);
                            leanh::lean_dec(v_h_x3f_6410_);
                            leanh::lean_dec(v___x_6137_);
                            leanh::lean_dec(v_stx_6119_);
                            v_a_6526_ = leanh::lean_ctor_get(v___x_6426_, 0);
                            v_isSharedCheck_6533_ =
                                (!leanh::lean_is_exclusive(v___x_6426_)) as u8;
                            if v_isSharedCheck_6533_ == 0 {
                                v___x_6528_ = v___x_6426_;
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6526_);
                                leanh::lean_dec(v___x_6426_);
                                v___x_6528_ = leanh::lean_box(0);
                                v_isShared_6529_ = v_isSharedCheck_6533_;
                                state = 32;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_6418_);
                        leanh::lean_dec(v_h_x3f_6410_);
                        leanh::lean_dec(v___x_6137_);
                        leanh::lean_dec(v_stx_6119_);
                        v_a_6534_ = leanh::lean_ctor_get(v___x_6422_, 0);
                        v_isSharedCheck_6541_ =
                            (!leanh::lean_is_exclusive(v___x_6422_)) as u8;
                        if v_isSharedCheck_6541_ == 0 {
                            v___x_6536_ = v___x_6422_;
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6534_);
                            leanh::lean_dec(v___x_6422_);
                            v___x_6536_ = leanh::lean_box(0);
                            v_isShared_6537_ = v_isSharedCheck_6541_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            18 => {
                leanh::lean_inc(v_a_6430_);
                v___x_6441_ = l_Lean_Level_succ___override(v_a_6430_);
                v___x_6442_ = l_Lean_mkSort(v___x_6441_);
                if v_isShared_6440_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6439_, 1);
                    leanh::lean_ctor_set(v___x_6439_, 0, v___x_6442_);
                    v___x_6444_ = v___x_6439_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6508_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 0, v___x_6442_);
                    v___x_6444_ = v_reuseFailAlloc_6508_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_6445_ = l_Lean_Elab_Do_elabDoFor___closed__14;
                v___x_6446_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_6444_,
                    v___x_6434_,
                    v___x_6445_,
                    v___y_6414_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                );
                if leanh::lean_obj_tag(v___x_6446_) == 0 {
                    v_a_6447_ = leanh::lean_ctor_get(v___x_6446_, 0);
                    v_isSharedCheck_6507_ = (!leanh::lean_is_exclusive(v___x_6446_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6449_ = v___x_6446_;
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6447_);
                        leanh::lean_dec(v___x_6446_);
                        v___x_6449_ = leanh::lean_box(0);
                        v_isShared_6450_ = v_isSharedCheck_6507_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_6437_);
                    leanh::lean_dec(v_a_6430_);
                    leanh::lean_dec(v_a_6428_);
                    leanh::lean_dec(v_a_6423_);
                    leanh::lean_dec(v_x_6418_);
                    leanh::lean_dec(v_h_x3f_6410_);
                    leanh::lean_dec(v___x_6137_);
                    leanh::lean_dec(v_stx_6119_);
                    return v___x_6446_;
                }
            }
            20 => {
                v___x_6451_ = leanh::lean_unsigned_to_nat(3);
                v___x_6452_ = l_Lean_Syntax_getArg(v___x_6137_, v___x_6451_);
                leanh::lean_dec(v___x_6137_);
                leanh::lean_inc(v_a_6447_);
                if v_isShared_6450_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6449_, 1);
                    v___x_6454_ = v___x_6449_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6447_);
                    v___x_6454_ = v_reuseFailAlloc_6506_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_6455_ = leanh::lean_box(0);
                v___x_6456_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_6452_,
                    v___x_6454_,
                    v___x_6139_,
                    v___x_6139_,
                    v___x_6455_,
                    v___y_6412_,
                    v___y_6413_,
                    v___y_6414_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                );
                if leanh::lean_obj_tag(v___x_6456_) == 0 {
                    v_a_6457_ = leanh::lean_ctor_get(v___x_6456_, 0);
                    leanh::lean_inc(v_a_6457_);
                    leanh::lean_dec_ref_known(v___x_6456_, 1);
                    v_body_6458_ = l_Lean_Syntax_getArg(v_stx_6119_, v___x_6451_);
                    leanh::lean_dec(v_stx_6119_);
                    leanh::lean_inc(v_body_6458_);
                    v___x_6459_ = l_Lean_Elab_Do_inferControlInfoSeq(
                        v_body_6458_,
                        v___y_6412_,
                        v___y_6413_,
                        v___y_6414_,
                        v___y_6415_,
                        v___y_6416_,
                        v___y_6417_,
                    );
                    if leanh::lean_obj_tag(v___x_6459_) == 0 {
                        v_a_6460_ = leanh::lean_ctor_get(v___x_6459_, 0);
                        leanh::lean_inc(v_a_6460_);
                        leanh::lean_dec_ref_known(v___x_6459_, 1);
                        v___x_6461_ = l_Lean_Elab_Do_getReturnCont___redArg(v___y_6411_);
                        if leanh::lean_obj_tag(v___x_6461_) == 0 {
                            v_a_6462_ = leanh::lean_ctor_get(v___x_6461_, 0);
                            leanh::lean_inc(v_a_6462_);
                            leanh::lean_dec_ref_known(v___x_6461_, 1);
                            v___x_6463_ = l_Lean_Elab_Do_elabDoFor___closed__16;
                            v___x_6464_ =
                                l_Lean_Core_mkFreshUserName(v___x_6463_, v___y_6416_, v___y_6417_);
                            if leanh::lean_obj_tag(v___x_6464_) == 0 {
                                v_a_6465_ = leanh::lean_ctor_get(v___x_6464_, 0);
                                leanh::lean_inc(v_a_6465_);
                                leanh::lean_dec_ref_known(v___x_6464_, 1);
                                v_monadInfo_6466_ = leanh::lean_ctor_get(v___y_6411_, 0);
                                v_mutVars_6467_ = leanh::lean_ctor_get(v___y_6411_, 1);
                                leanh::lean_inc(v_a_6437_);
                                v___f_6468_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    10,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_6468_, 0, v_a_6437_);
                                leanh::lean_inc_ref(v___f_6468_);
                                leanh::lean_inc(v_x_6418_);
                                v___f_6469_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__2___boxed
                                        as *mut core::ffi::c_void,
                                    5,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_6469_, 0, v_x_6418_);
                                leanh::lean_closure_set(v___f_6469_, 1, v___f_6468_);
                                leanh::lean_closure_set(v___f_6469_, 2, v___x_6132_);
                                v___x_6470_ = leanh::lean_box((v___x_6139_) as usize);
                                leanh::lean_inc(v_a_6462_);
                                v___f_6471_ = leanh::lean_alloc_closure(
                                    l_Lean_Elab_Do_elabDoFor___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    12,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_6471_, 0, v_a_6462_);
                                leanh::lean_closure_set(v___f_6471_, 1, v___x_6132_);
                                leanh::lean_closure_set(v___f_6471_, 2, v___x_6470_);
                                v___x_6472_ = lean_array_get_size(v_mutVars_6467_);
                                v___x_6473_ = l_Lean_Elab_Do_expandDoFor___closed__9;
                                v___x_6474_ = lean_nat_dec_lt(v___x_6136_, v___x_6472_);
                                if v___x_6474_ == 0 {
                                    leanh::lean_inc(v_x_6418_);
                                    leanh::lean_inc(v_a_6447_);
                                    leanh::lean_inc(v_a_6430_);
                                    leanh::lean_inc(v_a_6465_);
                                    leanh::lean_inc(v_a_6428_);
                                    leanh::lean_inc(v_a_6457_);
                                    leanh::lean_inc(v_h_x3f_6410_);
                                    leanh::lean_inc(v_a_6437_);
                                    v___y_6360_ = v_a_6437_;
                                    v___y_6361_ = v_h_x3f_6410_;
                                    v___y_6362_ = v___f_6471_;
                                    v___y_6363_ = v_a_6423_;
                                    v___y_6364_ = v___f_6468_;
                                    v___y_6365_ = v_a_6457_;
                                    v___y_6366_ = v_body_6458_;
                                    v___y_6367_ = v_a_6428_;
                                    v___y_6368_ = v_a_6465_;
                                    v___y_6369_ = v_a_6462_;
                                    v___y_6370_ = v___f_6469_;
                                    v___y_6371_ = v___x_6420_;
                                    v___y_6372_ = v_a_6430_;
                                    v___y_6373_ = v_a_6447_;
                                    v___y_6374_ = v_x_6418_;
                                    v___y_6375_ = v_monadInfo_6466_;
                                    v___y_6376_ = v_a_6437_;
                                    v___y_6377_ = v___y_6417_;
                                    v___y_6378_ = v_a_6460_;
                                    v___y_6379_ = v___y_6412_;
                                    v___y_6380_ = v___y_6415_;
                                    v___y_6381_ = v_h_x3f_6410_;
                                    v___y_6382_ = v___y_6416_;
                                    v___y_6383_ = v_a_6457_;
                                    v___y_6384_ = v___y_6413_;
                                    v___y_6385_ = v_a_6465_;
                                    v___y_6386_ = v_a_6428_;
                                    v___y_6387_ = v_a_6430_;
                                    v___y_6388_ = v___x_6434_;
                                    v___y_6389_ = v___y_6411_;
                                    v___y_6390_ = v___y_6414_;
                                    v___y_6391_ = v_a_6447_;
                                    v___y_6392_ = v_x_6418_;
                                    v___y_6393_ = v___x_6473_;
                                    state = 16;
                                    continue;
                                } else {
                                    v___x_6475_ = lean_nat_dec_le(v___x_6472_, v___x_6472_);
                                    if v___x_6475_ == 0 {
                                        if v___x_6474_ == 0 {
                                            leanh::lean_inc(v_x_6418_);
                                            leanh::lean_inc(v_a_6447_);
                                            leanh::lean_inc(v_a_6430_);
                                            leanh::lean_inc(v_a_6465_);
                                            leanh::lean_inc(v_a_6428_);
                                            leanh::lean_inc(v_a_6457_);
                                            leanh::lean_inc(v_h_x3f_6410_);
                                            leanh::lean_inc(v_a_6437_);
                                            v___y_6360_ = v_a_6437_;
                                            v___y_6361_ = v_h_x3f_6410_;
                                            v___y_6362_ = v___f_6471_;
                                            v___y_6363_ = v_a_6423_;
                                            v___y_6364_ = v___f_6468_;
                                            v___y_6365_ = v_a_6457_;
                                            v___y_6366_ = v_body_6458_;
                                            v___y_6367_ = v_a_6428_;
                                            v___y_6368_ = v_a_6465_;
                                            v___y_6369_ = v_a_6462_;
                                            v___y_6370_ = v___f_6469_;
                                            v___y_6371_ = v___x_6420_;
                                            v___y_6372_ = v_a_6430_;
                                            v___y_6373_ = v_a_6447_;
                                            v___y_6374_ = v_x_6418_;
                                            v___y_6375_ = v_monadInfo_6466_;
                                            v___y_6376_ = v_a_6437_;
                                            v___y_6377_ = v___y_6417_;
                                            v___y_6378_ = v_a_6460_;
                                            v___y_6379_ = v___y_6412_;
                                            v___y_6380_ = v___y_6415_;
                                            v___y_6381_ = v_h_x3f_6410_;
                                            v___y_6382_ = v___y_6416_;
                                            v___y_6383_ = v_a_6457_;
                                            v___y_6384_ = v___y_6413_;
                                            v___y_6385_ = v_a_6465_;
                                            v___y_6386_ = v_a_6428_;
                                            v___y_6387_ = v_a_6430_;
                                            v___y_6388_ = v___x_6434_;
                                            v___y_6389_ = v___y_6411_;
                                            v___y_6390_ = v___y_6414_;
                                            v___y_6391_ = v_a_6447_;
                                            v___y_6392_ = v_x_6418_;
                                            v___y_6393_ = v___x_6473_;
                                            state = 16;
                                            continue;
                                        } else {
                                            v___x_6476_ = 0usize;
                                            v___x_6477_ = lean_usize_of_nat(v___x_6472_);
                                            v___x_6478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_6460_, v_mutVars_6467_, v___x_6476_, v___x_6477_, v___x_6473_);
                                            leanh::lean_inc(v_x_6418_);
                                            leanh::lean_inc(v_a_6447_);
                                            leanh::lean_inc(v_a_6430_);
                                            leanh::lean_inc(v_a_6465_);
                                            leanh::lean_inc(v_a_6428_);
                                            leanh::lean_inc(v_a_6457_);
                                            leanh::lean_inc(v_h_x3f_6410_);
                                            leanh::lean_inc(v_a_6437_);
                                            v___y_6360_ = v_a_6437_;
                                            v___y_6361_ = v_h_x3f_6410_;
                                            v___y_6362_ = v___f_6471_;
                                            v___y_6363_ = v_a_6423_;
                                            v___y_6364_ = v___f_6468_;
                                            v___y_6365_ = v_a_6457_;
                                            v___y_6366_ = v_body_6458_;
                                            v___y_6367_ = v_a_6428_;
                                            v___y_6368_ = v_a_6465_;
                                            v___y_6369_ = v_a_6462_;
                                            v___y_6370_ = v___f_6469_;
                                            v___y_6371_ = v___x_6420_;
                                            v___y_6372_ = v_a_6430_;
                                            v___y_6373_ = v_a_6447_;
                                            v___y_6374_ = v_x_6418_;
                                            v___y_6375_ = v_monadInfo_6466_;
                                            v___y_6376_ = v_a_6437_;
                                            v___y_6377_ = v___y_6417_;
                                            v___y_6378_ = v_a_6460_;
                                            v___y_6379_ = v___y_6412_;
                                            v___y_6380_ = v___y_6415_;
                                            v___y_6381_ = v_h_x3f_6410_;
                                            v___y_6382_ = v___y_6416_;
                                            v___y_6383_ = v_a_6457_;
                                            v___y_6384_ = v___y_6413_;
                                            v___y_6385_ = v_a_6465_;
                                            v___y_6386_ = v_a_6428_;
                                            v___y_6387_ = v_a_6430_;
                                            v___y_6388_ = v___x_6434_;
                                            v___y_6389_ = v___y_6411_;
                                            v___y_6390_ = v___y_6414_;
                                            v___y_6391_ = v_a_6447_;
                                            v___y_6392_ = v_x_6418_;
                                            v___y_6393_ = v___x_6478_;
                                            state = 16;
                                            continue;
                                        }
                                    } else {
                                        v___x_6479_ = 0usize;
                                        v___x_6480_ = lean_usize_of_nat(v___x_6472_);
                                        v___x_6481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_elabDoFor_spec__7(v_a_6460_, v_mutVars_6467_, v___x_6479_, v___x_6480_, v___x_6473_);
                                        leanh::lean_inc(v_x_6418_);
                                        leanh::lean_inc(v_a_6447_);
                                        leanh::lean_inc(v_a_6430_);
                                        leanh::lean_inc(v_a_6465_);
                                        leanh::lean_inc(v_a_6428_);
                                        leanh::lean_inc(v_a_6457_);
                                        leanh::lean_inc(v_h_x3f_6410_);
                                        leanh::lean_inc(v_a_6437_);
                                        v___y_6360_ = v_a_6437_;
                                        v___y_6361_ = v_h_x3f_6410_;
                                        v___y_6362_ = v___f_6471_;
                                        v___y_6363_ = v_a_6423_;
                                        v___y_6364_ = v___f_6468_;
                                        v___y_6365_ = v_a_6457_;
                                        v___y_6366_ = v_body_6458_;
                                        v___y_6367_ = v_a_6428_;
                                        v___y_6368_ = v_a_6465_;
                                        v___y_6369_ = v_a_6462_;
                                        v___y_6370_ = v___f_6469_;
                                        v___y_6371_ = v___x_6420_;
                                        v___y_6372_ = v_a_6430_;
                                        v___y_6373_ = v_a_6447_;
                                        v___y_6374_ = v_x_6418_;
                                        v___y_6375_ = v_monadInfo_6466_;
                                        v___y_6376_ = v_a_6437_;
                                        v___y_6377_ = v___y_6417_;
                                        v___y_6378_ = v_a_6460_;
                                        v___y_6379_ = v___y_6412_;
                                        v___y_6380_ = v___y_6415_;
                                        v___y_6381_ = v_h_x3f_6410_;
                                        v___y_6382_ = v___y_6416_;
                                        v___y_6383_ = v_a_6457_;
                                        v___y_6384_ = v___y_6413_;
                                        v___y_6385_ = v_a_6465_;
                                        v___y_6386_ = v_a_6428_;
                                        v___y_6387_ = v_a_6430_;
                                        v___y_6388_ = v___x_6434_;
                                        v___y_6389_ = v___y_6411_;
                                        v___y_6390_ = v___y_6414_;
                                        v___y_6391_ = v_a_6447_;
                                        v___y_6392_ = v_x_6418_;
                                        v___y_6393_ = v___x_6481_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_6462_);
                                leanh::lean_dec(v_a_6460_);
                                leanh::lean_dec(v_body_6458_);
                                leanh::lean_dec(v_a_6457_);
                                leanh::lean_dec(v_a_6447_);
                                leanh::lean_dec(v_a_6437_);
                                leanh::lean_dec(v_a_6430_);
                                leanh::lean_dec(v_a_6428_);
                                leanh::lean_dec(v_a_6423_);
                                leanh::lean_dec(v_x_6418_);
                                leanh::lean_dec(v_h_x3f_6410_);
                                v_a_6482_ = leanh::lean_ctor_get(v___x_6464_, 0);
                                v_isSharedCheck_6489_ =
                                    (!leanh::lean_is_exclusive(v___x_6464_)) as u8;
                                if v_isSharedCheck_6489_ == 0 {
                                    v___x_6484_ = v___x_6464_;
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6482_);
                                    leanh::lean_dec(v___x_6464_);
                                    v___x_6484_ = leanh::lean_box(0);
                                    v_isShared_6485_ = v_isSharedCheck_6489_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_6460_);
                            leanh::lean_dec(v_body_6458_);
                            leanh::lean_dec(v_a_6457_);
                            leanh::lean_dec(v_a_6447_);
                            leanh::lean_dec(v_a_6437_);
                            leanh::lean_dec(v_a_6430_);
                            leanh::lean_dec(v_a_6428_);
                            leanh::lean_dec(v_a_6423_);
                            leanh::lean_dec(v_x_6418_);
                            leanh::lean_dec(v_h_x3f_6410_);
                            v_a_6490_ = leanh::lean_ctor_get(v___x_6461_, 0);
                            v_isSharedCheck_6497_ =
                                (!leanh::lean_is_exclusive(v___x_6461_)) as u8;
                            if v_isSharedCheck_6497_ == 0 {
                                v___x_6492_ = v___x_6461_;
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6490_);
                                leanh::lean_dec(v___x_6461_);
                                v___x_6492_ = leanh::lean_box(0);
                                v_isShared_6493_ = v_isSharedCheck_6497_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_body_6458_);
                        leanh::lean_dec(v_a_6457_);
                        leanh::lean_dec(v_a_6447_);
                        leanh::lean_dec(v_a_6437_);
                        leanh::lean_dec(v_a_6430_);
                        leanh::lean_dec(v_a_6428_);
                        leanh::lean_dec(v_a_6423_);
                        leanh::lean_dec(v_x_6418_);
                        leanh::lean_dec(v_h_x3f_6410_);
                        v_a_6498_ = leanh::lean_ctor_get(v___x_6459_, 0);
                        v_isSharedCheck_6505_ =
                            (!leanh::lean_is_exclusive(v___x_6459_)) as u8;
                        if v_isSharedCheck_6505_ == 0 {
                            v___x_6500_ = v___x_6459_;
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6498_);
                            leanh::lean_dec(v___x_6459_);
                            v___x_6500_ = leanh::lean_box(0);
                            v_isShared_6501_ = v_isSharedCheck_6505_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6447_);
                    leanh::lean_dec(v_a_6437_);
                    leanh::lean_dec(v_a_6430_);
                    leanh::lean_dec(v_a_6428_);
                    leanh::lean_dec(v_a_6423_);
                    leanh::lean_dec(v_x_6418_);
                    leanh::lean_dec(v_h_x3f_6410_);
                    leanh::lean_dec(v_stx_6119_);
                    return v___x_6456_;
                }
            }
            22 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
                    v___x_6487_ = v_reuseFailAlloc_6488_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6487_;
            }
            24 => {
                if v_isShared_6493_ == 0 {
                    v___x_6495_ = v___x_6492_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_a_6490_);
                    v___x_6495_ = v_reuseFailAlloc_6496_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6495_;
            }
            26 => {
                if v_isShared_6501_ == 0 {
                    v___x_6503_ = v___x_6500_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
                    v___x_6503_ = v_reuseFailAlloc_6504_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6503_;
            }
            28 => {
                if v_isShared_6513_ == 0 {
                    v___x_6515_ = v___x_6512_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6516_, 0, v_a_6510_);
                    v___x_6515_ = v_reuseFailAlloc_6516_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6515_;
            }
            30 => {
                if v_isShared_6521_ == 0 {
                    v___x_6523_ = v___x_6520_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6524_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
                    v___x_6523_ = v_reuseFailAlloc_6524_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6523_;
            }
            32 => {
                if v_isShared_6529_ == 0 {
                    v___x_6531_ = v___x_6528_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
                    v___x_6531_ = v_reuseFailAlloc_6532_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6531_;
            }
            34 => {
                if v_isShared_6537_ == 0 {
                    v___x_6539_ = v___x_6536_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_6540_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
                    v___x_6539_ = v_reuseFailAlloc_6540_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_6539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Do_elabDoFor___boxed(
    mut v_stx_6550_: *mut leanh::LeanObject,
    mut v_dec_6551_: *mut leanh::LeanObject,
    mut v_a_6552_: *mut leanh::LeanObject,
    mut v_a_6553_: *mut leanh::LeanObject,
    mut v_a_6554_: *mut leanh::LeanObject,
    mut v_a_6555_: *mut leanh::LeanObject,
    mut v_a_6556_: *mut leanh::LeanObject,
    mut v_a_6557_: *mut leanh::LeanObject,
    mut v_a_6558_: *mut leanh::LeanObject,
    mut v_a_6559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6560_ = l_Lean_Elab_Do_elabDoFor(
        v_stx_6550_,
        v_dec_6551_,
        v_a_6552_,
        v_a_6553_,
        v_a_6554_,
        v_a_6555_,
        v_a_6556_,
        v_a_6557_,
        v_a_6558_,
    );
    leanh::lean_dec(v_a_6558_);
    leanh::lean_dec_ref(v_a_6557_);
    leanh::lean_dec(v_a_6556_);
    leanh::lean_dec_ref(v_a_6555_);
    leanh::lean_dec(v_a_6554_);
    leanh::lean_dec_ref(v_a_6553_);
    leanh::lean_dec_ref(v_a_6552_);
    return v_res_6560_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(
    mut v_00_u03b1_6561_: *mut leanh::LeanObject,
    mut v_msg_6562_: *mut leanh::LeanObject,
    mut v___y_6563_: *mut leanh::LeanObject,
    mut v___y_6564_: *mut leanh::LeanObject,
    mut v___y_6565_: *mut leanh::LeanObject,
    mut v___y_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___redArg(
        v_msg_6562_,
        v___y_6563_,
        v___y_6564_,
        v___y_6565_,
        v___y_6566_,
        v___y_6567_,
        v___y_6568_,
    );
    return v___x_6570_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2___boxed(
    mut v_00_u03b1_6571_: *mut leanh::LeanObject,
    mut v_msg_6572_: *mut leanh::LeanObject,
    mut v___y_6573_: *mut leanh::LeanObject,
    mut v___y_6574_: *mut leanh::LeanObject,
    mut v___y_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6580_ = l_Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2(
        v_00_u03b1_6571_,
        v_msg_6572_,
        v___y_6573_,
        v___y_6574_,
        v___y_6575_,
        v___y_6576_,
        v___y_6577_,
        v___y_6578_,
    );
    leanh::lean_dec(v___y_6578_);
    leanh::lean_dec_ref(v___y_6577_);
    leanh::lean_dec(v___y_6576_);
    leanh::lean_dec_ref(v___y_6575_);
    leanh::lean_dec(v___y_6574_);
    leanh::lean_dec_ref(v___y_6573_);
    return v_res_6580_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(
    mut v_00_u03b1_6581_: *mut leanh::LeanObject,
    mut v_name_6582_: *mut leanh::LeanObject,
    mut v_type_6583_: *mut leanh::LeanObject,
    mut v_k_6584_: *mut leanh::LeanObject,
    mut v___y_6585_: *mut leanh::LeanObject,
    mut v___y_6586_: *mut leanh::LeanObject,
    mut v___y_6587_: *mut leanh::LeanObject,
    mut v___y_6588_: *mut leanh::LeanObject,
    mut v___y_6589_: *mut leanh::LeanObject,
    mut v___y_6590_: *mut leanh::LeanObject,
    mut v___y_6591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6593_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___redArg(
        v_name_6582_,
        v_type_6583_,
        v_k_6584_,
        v___y_6585_,
        v___y_6586_,
        v___y_6587_,
        v___y_6588_,
        v___y_6589_,
        v___y_6590_,
        v___y_6591_,
    );
    return v___x_6593_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5___boxed(
    mut v_00_u03b1_6594_: *mut leanh::LeanObject,
    mut v_name_6595_: *mut leanh::LeanObject,
    mut v_type_6596_: *mut leanh::LeanObject,
    mut v_k_6597_: *mut leanh::LeanObject,
    mut v___y_6598_: *mut leanh::LeanObject,
    mut v___y_6599_: *mut leanh::LeanObject,
    mut v___y_6600_: *mut leanh::LeanObject,
    mut v___y_6601_: *mut leanh::LeanObject,
    mut v___y_6602_: *mut leanh::LeanObject,
    mut v___y_6603_: *mut leanh::LeanObject,
    mut v___y_6604_: *mut leanh::LeanObject,
    mut v___y_6605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6606_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Do_elabDoFor_spec__5(
        v_00_u03b1_6594_,
        v_name_6595_,
        v_type_6596_,
        v_k_6597_,
        v___y_6598_,
        v___y_6599_,
        v___y_6600_,
        v___y_6601_,
        v___y_6602_,
        v___y_6603_,
        v___y_6604_,
    );
    leanh::lean_dec(v___y_6604_);
    leanh::lean_dec_ref(v___y_6603_);
    leanh::lean_dec(v___y_6602_);
    leanh::lean_dec_ref(v___y_6601_);
    leanh::lean_dec(v___y_6600_);
    leanh::lean_dec_ref(v___y_6599_);
    leanh::lean_dec_ref(v___y_6598_);
    return v_res_6606_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(
    mut v_msgData_6607_: *mut leanh::LeanObject,
    mut v_macroStack_6608_: *mut leanh::LeanObject,
    mut v___y_6609_: *mut leanh::LeanObject,
    mut v___y_6610_: *mut leanh::LeanObject,
    mut v___y_6611_: *mut leanh::LeanObject,
    mut v___y_6612_: *mut leanh::LeanObject,
    mut v___y_6613_: *mut leanh::LeanObject,
    mut v___y_6614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6616_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___redArg(v_msgData_6607_, v_macroStack_6608_, v___y_6613_);
    return v___x_6616_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3___boxed(
    mut v_msgData_6617_: *mut leanh::LeanObject,
    mut v_macroStack_6618_: *mut leanh::LeanObject,
    mut v___y_6619_: *mut leanh::LeanObject,
    mut v___y_6620_: *mut leanh::LeanObject,
    mut v___y_6621_: *mut leanh::LeanObject,
    mut v___y_6622_: *mut leanh::LeanObject,
    mut v___y_6623_: *mut leanh::LeanObject,
    mut v___y_6624_: *mut leanh::LeanObject,
    mut v___y_6625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6626_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_elabDoFor_spec__2_spec__3(v_msgData_6617_, v_macroStack_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_);
    leanh::lean_dec(v___y_6624_);
    leanh::lean_dec_ref(v___y_6623_);
    leanh::lean_dec(v___y_6622_);
    leanh::lean_dec_ref(v___y_6621_);
    leanh::lean_dec(v___y_6620_);
    leanh::lean_dec_ref(v___y_6619_);
    return v_res_6626_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1()
-> *mut leanh::LeanObject {
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6634_ = l_Lean_Elab_Do_doElemElabAttribute;
    v___x_6635_ = l_Lean_Elab_Do_expandDoFor___closed__1;
    v___x_6636_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___closed__1;
    v___x_6637_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Do_elabDoFor___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_6638_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6634_,
        v___x_6635_,
        v___x_6636_,
        v___x_6637_,
    );
    return v___x_6638_;
}
pub unsafe fn l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1___boxed(
    mut v_a_6639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6640_ = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    return v_res_6640_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_BuiltinDo_For(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ProdN(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_expandDoFor___regBuiltin_Lean_Elab_Do_expandDoFor__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_BuiltinDo_For_0__Lean_Elab_Do_elabDoFor___regBuiltin_Lean_Elab_Do_elabDoFor__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_BuiltinDo_For(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Parser_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_BuiltinDo_For(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_BuiltinDo_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ProdN(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_BuiltinDo_For(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_BuiltinDo_For(builtin);
}